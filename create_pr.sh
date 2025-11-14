#!/bin/bash

# Create pull request using gh CLI
gh pr create \
  --title "Add GitHub issues listing script" \
  --body "$(cat <<'EOF'
## Summary

Added a bash script to list GitHub issues using the GitHub API, since the `gh` CLI tool has permission restrictions for direct use.

## Changes

- **list_issues.sh**: Bash script that fetches and displays GitHub issues
  - Uses curl to access GitHub REST API
  - Filters out pull requests to show only issues
  - Displays both open and closed issues with color-coded, formatted output
  - Accepts state parameter (open/closed/all)

- **github_issues_list.txt**: Complete snapshot of all repository issues at time of creation

## Technical Details

The script uses the GitHub REST API (`https://api.github.com/repos/konard/p-vs-np/issues`) to fetch issues and parses the JSON response using Python for clean formatting.

## Usage

```bash
bash list_issues.sh
```

This provides a convenient way to view repository issues from the command line without needing the gh CLI tool.
EOF
)"
