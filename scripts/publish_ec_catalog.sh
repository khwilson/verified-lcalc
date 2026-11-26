#!/usr/bin/env bash
set -euo pipefail

releases() {
  gh api --paginate --slurp "repos/$GITHUB_REPOSITORY/releases?per_page=100"
}

retry_read() {
  local delay
  for delay in 1 2 4 8 16; do
    if "$@"; then
      return 0
    fi
    sleep "$delay"
  done
  "$@"
}

find_release() {
  releases | jq -c --arg tag "$1" 'first(.[][] | select(.tag_name == $tag)) // empty'
}

draft_visible() {
  find_release "$1" | jq -es --argjson id "$2" \
    'length == 1 and .[0].id == $id and .[0].draft == true' >/dev/null
}

verify_replay_assets() {
  local release_id=$1 export_dir=$2 uploaded name digest
  uploaded=$(gh api --paginate --slurp \
    "repos/$GITHUB_REPOSITORY/releases/$release_id/assets?per_page=100") || return
  for name in catalog.json witnesses.jsonl.gz provenance.sigstore.json; do
    digest=$(sha256sum -- "$export_dir/$name")
    if ! jq -e --arg name "$name" --arg digest "sha256:${digest%% *}" \
      'any(.[][]; .name == $name and .state == "uploaded" and .digest == $digest)' \
      <<< "$uploaded" >/dev/null; then
      echo "$name is missing or differs from the attested artifact on release $release_id." >&2
      return 1
    fi
  done
}

published_catalog_index() {
  local listed
  listed=$(releases) || return
  jq -e --arg current "$1" '[
    .[][] | select(.prerelease and (.draft | not))
    | select(.tag_name | test("^ec-certificates-[0-9]+-[0-9]+$"))
  ] | sort_by(.published_at, .id) | reverse | map(.tag_name + ".json")
  | select($current == "" or index($current + ".json") != null)' <<< "$listed"
}

case "$1" in
  release)
    tag=$2
    export_dir=$3
    [[ "$tag" =~ ^ec-certificates-[0-9]+-[0-9]+$ ]]
    test -s "$export_dir/catalog.json"
    test -s "$export_dir/witnesses.jsonl.gz"
    test -s "$export_dir/provenance.sigstore.json"
    assets=("$export_dir"/*)
    if (( ${#assets[@]} > 1000 )); then
      echo "GitHub allows 1,000 assets per release. Rerun with a smaller count and use offsets for subsequent slices." >&2
      exit 1
    fi
    for asset in "${assets[@]}"; do
      test -f "$asset" && test ! -L "$asset" || exit 1
    done

    release=$(find_release "$tag")
    title=$(node --input-type=module -e '
      import {readFileSync} from "node:fs";
      import {releaseTitle} from "./web/certificates/batch-display.mjs";
      const [path, tag] = process.argv.slice(1);
      console.log(releaseTitle(JSON.parse(readFileSync(path, "utf8")), tag));
    ' "$export_dir/catalog.json" "$tag")
    if [[ -z "$release" ]]; then
      release=$(gh api --method POST "repos/$GITHUB_REPOSITORY/releases" \
        -f tag_name="$tag" -f target_commitish="$GITHUB_SHA" \
        -F draft=true -F prerelease=true -f make_latest=false \
        -f name="$title" \
        -f body="Audited Lean certificates with signed replay records from $GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID.")
    fi
    release_id=$(jq -er --arg tag "$tag" --arg sha "$GITHUB_SHA" '
      select(.tag_name == $tag and .target_commitish == $sha and .prerelease == true)
      | .id | select(type == "number")' <<< "$release")
    if jq -e '.draft == false' <<< "$release" >/dev/null; then
      retry_read verify_replay_assets "$release_id" "$export_dir"
      echo "$tag is already published."
      exit 0
    fi
    # Replacement is allowed only before publication, for retries after an interrupted upload.
    # gh release upload resolves drafts by tag, so wait for its listing to see this exact draft.
    retry_read draft_visible "$tag" "$release_id"
    gh release upload "$tag" --repo "$GITHUB_REPOSITORY" --clobber "${assets[@]}"
    retry_read verify_replay_assets "$release_id" "$export_dir"
    gh api --method PATCH "repos/$GITHUB_REPOSITORY/releases/$release_id" \
      -F draft=false -f name="$title" -f make_latest=false --silent
    ;;
  site)
    tag=$2
    site_dir=$3
    mkdir -p "$site_dir/catalogs"
    cp -R web/certificates/. "$site_dir/"
    node --input-type=module -e '
      import {readFileSync, writeFileSync} from "node:fs";
      const [revision, ...paths] = process.argv.slice(1);
      if (!/^[0-9a-f]{40}$/.test(revision)) throw new Error("Invalid companion source revision");
      for (const path of paths) {
        const report = JSON.parse(readFileSync(path, "utf8"));
        writeFileSync(path, JSON.stringify({...report, git_revision: revision}, null, 2) + "\n");
      }
    ' "$GITHUB_SHA" "$site_dir/fixture-field-coverage.json" "$site_dir/field-dependency-roadmap.json"
    retry_read published_catalog_index "$tag" > "$site_dir/catalogs/index.json"
    basenames=$(jq -r '.[]' "$site_dir/catalogs/index.json")
    while IFS= read -r basename; do
      [[ -n "$basename" ]] || continue
      gh release download "${basename%.json}" --repo "$GITHUB_REPOSITORY" \
        --pattern catalog.json --output "$site_dir/catalogs/$basename"
    done <<< "$basenames"
    ;;
  *)
    echo "Expected release or site command." >&2
    exit 2
    ;;
esac
