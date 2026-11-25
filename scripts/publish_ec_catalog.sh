#!/usr/bin/env bash
set -euo pipefail

releases() {
  gh api --paginate --slurp "repos/$GITHUB_REPOSITORY/releases?per_page=100"
}

case "$1" in
  release)
    tag=$2
    export_dir=$3
    [[ "$tag" =~ ^ec-certificates-[0-9]+-[0-9]+$ ]]
    test -s "$export_dir/catalog.json"
    assets=("$export_dir"/*)
    if (( ${#assets[@]} > 1000 )); then
      echo "GitHub allows 1,000 assets per release. Rerun with a smaller count and use offsets for subsequent slices." >&2
      exit 1
    fi
    for asset in "${assets[@]}"; do
      test -f "$asset" && test ! -L "$asset" || exit 1
    done

    release=$(releases | jq -c --arg tag "$tag" '[.[][] | select(.tag_name == $tag)] | first // empty')
    if [[ -z "$release" ]]; then
      gh release create "$tag" --repo "$GITHUB_REPOSITORY" --target "$GITHUB_SHA" \
        --draft --prerelease --latest=false --title "Elliptic curve certificates $tag" \
        --notes "Audited Lean certificates from $GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID."
    else
      jq -e --arg sha "$GITHUB_SHA" '.prerelease and .target_commitish == $sha' <<< "$release" >/dev/null
      if jq -e '.draft == false' <<< "$release" >/dev/null; then
        jq -e '.assets | any(.name == "catalog.json" and .state == "uploaded")' <<< "$release" >/dev/null
        echo "$tag is already published."
        exit 0
      fi
    fi
    # Replacement is allowed only before publication, for retries after an interrupted upload.
    gh release upload "$tag" --repo "$GITHUB_REPOSITORY" --clobber "${assets[@]}"
    gh release edit "$tag" --repo "$GITHUB_REPOSITORY" --draft=false --latest=false
    ;;
  site)
    tag=$2
    site_dir=$3
    mkdir -p "$site_dir/catalogs"
    cp -R web/certificates/. "$site_dir/"
    releases | jq '[
      .[][] | select(.prerelease and (.draft | not))
      | select(.tag_name | test("^ec-certificates-[0-9]+-[0-9]+$"))
    ] | sort_by(.published_at, .id) | reverse | map(.tag_name + ".json")' > "$site_dir/catalogs/index.json"
    jq -e --arg current "$tag.json" 'index($current) != null' "$site_dir/catalogs/index.json" >/dev/null
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
