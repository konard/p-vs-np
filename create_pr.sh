#!/bin/bash

# GitHub CLI is installed at /tmp/gh_2.62.0_linux_amd64/bin/gh
# To use it, you need to authenticate first:
#   /tmp/gh_2.62.0_linux_amd64/bin/gh auth login
# Or set the GH_TOKEN environment variable:
#   export GH_TOKEN=your_github_token

GH_BIN="/tmp/gh_2.62.0_linux_amd64/bin/gh"

# Create pull request using gh CLI
$GH_BIN pr create \
  --title "Add GitHub issues listing script" \
  --body "$(cat <<'EOF'
## Summary

Added a bash script to list GitHub issues using the GitHub API.

## Changes

- **list_issues.sh**: Bash script that fetches and displays GitHub issues
  - Uses curl to access GitHub REST API
  - Filters out pull requests to show only issues
  - Displays both open and closed issues with color-coded, formatted output

- **github_issues_list.txt**: Complete snapshot of all repository issues

- **create_pr.sh**: Script template for creating pull requests with gh CLI

## Technical Details

The script uses the GitHub REST API (`https://api.github.com/repos/konard/p-vs-np/issues`) to fetch issues and parses the JSON response using Python for clean formatting.

## Usage

```bash
bash list_issues.sh
```

This provides a convenient way to view repository issues from the command line.
EOF
)"
