#!/usr/bin/env python3
"""Cross-compile the numerical Lean worker; publish only after native/WASM parity.
Requires an externally built, exact-toolchain wasm64 Lean runtime (see README).
Never attempts to link native Lean archives into WebAssembly.
"""

import argparse
import json
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path

from lcalc_registry.checker.environment import Environment, file_hash
from lcalc_registry.checker.protocol import canonical

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "worker"


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--runtime",
        type=Path,
        required=True,
        help="Trusted runtime.json; library/include paths are relative to it",
    )
    p.add_argument("--emcc", default="emcc")
    p.add_argument("--node", default="node")
    p.add_argument(
        "--node-arg",
        action="append",
        default=[],
        help="For example --node-arg=--experimental-wasm-memory64 on older Node",
    )
    p.add_argument(
        "--output", type=Path, default=ROOT / "experiments/browser-worker/web/wasm"
    )
    args = p.parse_args()
    if shutil.which(args.emcc) is None:
        p.error("Emscripten is unavailable; install it outside this restricted session")
    runtime = json.loads(args.runtime.read_text())
    home = args.runtime.resolve().parent
    env = Environment()
    toolchain = env.build_config["toolchain"]
    if (
        runtime.get("schema") != "lcalc.lean-wasm-runtime.v1"
        or runtime.get("lean_toolchain") != toolchain
        or runtime.get("target") != "wasm64"
        or runtime.get("threads") is not False
    ):
        p.error("Require exact Lean toolchain, wasm64, single-threaded runtime")
    includes = [home / x for x in runtime["include_dirs"]]
    libraries = []
    for item in runtime["libraries"]:
        lib = home / item["path"]
        if file_hash(lib) != item["sha256"]:
            p.error("Runtime library digest mismatch: " + str(lib))
        libraries.append(lib)
    if not libraries or not any((x / "lean/lean.h").exists() for x in includes):
        p.error("Runtime headers or libraries missing")
    config = env.build_config
    sources = [Path(str(x).removesuffix(".o.export")) for x in config["core_objects"]]
    sources += [env.build / "lib/lean/LcalcVolunteer/Core.c", BASE / "bridge.c"]
    if any(not x.is_file() for x in sources):
        p.error("Run build_native.py and build the existing core first")
    # The provider is trusted build input; it supplies GMP/runtime system flags.
    with tempfile.TemporaryDirectory(prefix="lcalc-wasm-") as tmp:
        tmp = Path(tmp)
        objects = []
        common = [
            "-O3",
            "-sMEMORY64=1",
            *runtime.get("compile_flags", []),
            *[flag for x in includes for flag in ["-I", str(x)]],
        ]
        for i, source in enumerate(sources):
            obj = tmp / f"{i}.o"
            subprocess.run(
                [args.emcc, *common, "-c", str(source), "-o", str(obj)], check=True
            )
            objects.append(obj)
        loader = tmp / "worker.mjs"
        link = [
            args.emcc,
            *common,
            *map(str, objects),
            "-Wl,--start-group",
            *map(str, libraries),
            "-Wl,--end-group",
            *runtime.get("link_flags", []),
            "-sALLOW_MEMORY_GROWTH=1",
            "-sMODULARIZE=1",
            "-sEXPORT_ES6=1",
            "-sENVIRONMENT=web,worker,node",
            "-sWASM_BIGINT=1",
            "-sNO_EXIT_RUNTIME=1",
            '-sEXPORTED_FUNCTIONS=["_lcalc_worker_init","_lcalc_worker_compute"]',
            '-sEXPORTED_RUNTIME_METHODS=["ccall"]',
            "-o",
            str(loader),
        ]
        subprocess.run(link, check=True)
        subprocess.run(
            [
                args.node,
                *args.node_arg,
                str(BASE / "test_wasm.mjs"),
                str(loader),
                str(env.worker),
            ],
            check=True,
        )
        env.check_immutable()
        args.output.mkdir(parents=True, exist_ok=True)
        files = {}
        for role, file in [("loader", loader), ("wasm", tmp / "worker.wasm")]:
            target = args.output / file.name
            shutil.copyfile(file, target)
            files[role] = {
                "path": "/static/wasm/" + target.name,
                "sha256": file_hash(target),
                "size": target.stat().st_size,
            }
        # Publish corresponding numerical sources and notices alongside the bundle.
        with tarfile.open(args.output / "sources.tar.gz", "w:gz") as tar:
            for obj in config["core_objects"]:
                relative = Path(
                    str(Path(obj).relative_to(ROOT / ".lake/build/ir")).removesuffix(
                        ".c.o.export"
                    )
                    + ".lean"
                )
                tar.add(ROOT / relative, arcname=str(relative))
            tar.add(
                ROOT / "data/upstream/pari-elliptic-wild.c",
                arcname="data/upstream/pari-elliptic-wild.c",
            )
            for tool in ["build_native.py", "build_wasm.py"]:
                tar.add(
                    ROOT / "lcalc_registry/tools" / tool,
                    arcname="lcalc_registry/tools/" + tool,
                )
            for source in (BASE / "lean").rglob("*.lean"):
                tar.add(source, arcname=str(source.relative_to(ROOT)))
            tar.add(BASE / "test_wasm.mjs", arcname="worker/test_wasm.mjs")
            tar.add(BASE / "bridge.c", arcname="worker/bridge.c")
            tar.add(ROOT / "LICENSES", arcname="LICENSES")
        manifest = {
            "schema": "lcalc.wasm-worker.v1",
            "abi": "lcalc-worker-text-v1",
            "target": "wasm64",
            "threads": False,
            "lean_toolchain": toolchain,
            "checker_sources": env.files,
            "files": files,
            "runtime_manifest_sha256": file_hash(args.runtime),
            "self_test": "native-wasm-exact-json:11.a2,37.a1,112.a1",
            "source_archive": {
                "path": "/static/wasm/sources.tar.gz",
                "sha256": file_hash(args.output / "sources.tar.gz"),
            },
        }
        temporary = args.output / "manifest.json.tmp"
        temporary.write_bytes(canonical(manifest))
        temporary.replace(args.output / "manifest.json")
        print(json.dumps({"output": str(args.output), "files": files}, indent=2))


if __name__ == "__main__":
    main()
