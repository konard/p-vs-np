#!/bin/bash

# GitHub repository details
OWNER="konard"
REPO="p-vs-np"

# Colors for terminal output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}Fetching issues for ${OWNER}/${REPO}...${NC}"
echo "=========================================="
echo ""

# Function to display issues
display_issues() {
    local state=$1
    local label=$2

    echo -e "${YELLOW}${label}${NC}"
    echo ""

    # Fetch and parse issues
    curl -s "https://api.github.com/repos/${OWNER}/${REPO}/issues?state=${state}&per_page=100" | \
    python3 -c "
import sys, json

try:
    data = json.load(sys.stdin)
    issues = [item for item in data if 'pull_request' not in item]

    if not issues:
        print('  No ${state} issues found.')
    else:
        for issue in issues:
            num = issue['number']
            title = issue['title']
            state = issue['state']
            created = issue['created_at'][:10]
            url = issue['html_url']
            labels = ', '.join([l['name'] for l in issue.get('labels', [])])

            print(f'Issue #{num}: {title}')
            print(f'  State: {state}')
            print(f'  Created: {created}')
            print(f'  URL: {url}')
            if labels:
                print(f'  Labels: {labels}')
            print()
except Exception as e:
    print(f'Error parsing JSON: {e}', file=sys.stderr)
"
}

# Display open issues
display_issues "open" "OPEN ISSUES:"

echo ""
echo "=========================================="
echo ""

# Display closed issues (last 20)
display_issues "closed" "RECENTLY CLOSED ISSUES (showing recent):"
