#!/usr/bin/env python3
"""
Create GitHub issues for each P vs NP attempt.
Each issue will be a sub-issue of #44.
"""

import json
import subprocess
import time
import sys

def create_issue(attempt, parent_issue_number=44, repo="konard/p-vs-np", dry_run=False):
    """
    Create a GitHub issue for a single P vs NP attempt.

    Args:
        attempt: Dictionary with id, author, year, claim, description
        parent_issue_number: Issue number to reference as parent (default: 44)
        repo: Repository in format owner/repo
        dry_run: If True, just print what would be created without creating
    """
    # Create a folder name from author and year
    # Use lowercase, replace spaces with hyphens
    author_slug = attempt['author'].lower().replace(' ', '-').replace('.', '')
    if author_slug == 'unknown':
        author_slug = f"attempt-{attempt['id']}"

    folder_name = f"{author_slug}-{attempt['year']}-{attempt['claim'].replace('≠', 'neq').replace('=', 'eq').lower()}"

    # Clean up folder name - remove invalid characters
    folder_name = ''.join(c for c in folder_name if c.isalnum() or c in '-_')

    # Create issue title
    title = f"Formalize {attempt['author']} ({attempt['year']}) - {attempt['claim']}"
    if len(title) > 100:
        title = f"Formalize {attempt['year']} {attempt['claim']} attempt #{attempt['id']}"

    # Create issue body
    body = f"""## P vs NP Attempt Formalization

**Attempt ID:** {attempt['id']}
**Author:** {attempt['author']}
**Year:** {attempt['year']}
**Claim:** {attempt['claim']}
**Folder:** `proofs/attempts/{folder_name}/`

### Description

{attempt['description']}

### Task

This issue tracks the formal verification of this P vs NP proof attempt. The goal is to:

1. Create folder `proofs/attempts/{folder_name}/`
2. Add a `README.md` describing the attempt
3. Write formal proofs in:
   - Coq (`coq/`)
   - Lean (`lean/`)
   - Isabelle (`isabelle/`)
4. Formalize the proof until the mistake/gap is found
5. Document the error in the README

### Source

From Woeginger's list: https://wscor.win.tue.nl/woeginger/P-versus-NP.htm

### Parent Issue

Part of #44 - Test all P vs NP attempts formally

---

*This issue was created automatically by the AI issue solver for #45*
"""

    if dry_run:
        print(f"\n{'='*80}")
        print(f"Would create issue #{attempt['id']}:")
        print(f"Title: {title}")
        print(f"Folder: {folder_name}")
        print(f"Body preview (first 200 chars): {body[:200]}...")
        return folder_name

    # Create the issue using gh CLI
    try:
        # Escape quotes in title and body
        title_escaped = title.replace('"', '\\"')

        # Write body to a temp file to avoid shell quoting issues
        temp_body_file = f"/tmp/issue_body_{attempt['id']}.md"
        with open(temp_body_file, 'w') as f:
            f.write(body)

        # Create the issue
        cmd = [
            'gh', 'issue', 'create',
            '--repo', repo,
            '--title', title,
            '--body-file', temp_body_file,
            '--label', 'formal-verification',
            '--label', 'attempt-formalization'
        ]

        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
        issue_url = result.stdout.strip()

        print(f"Created issue #{attempt['id']}: {issue_url}")

        # Clean up temp file
        subprocess.run(['rm', temp_body_file], check=False)

        # Rate limiting - don't create issues too fast
        time.sleep(1)

        return issue_url

    except subprocess.CalledProcessError as e:
        print(f"Error creating issue for attempt #{attempt['id']}: {e}", file=sys.stderr)
        print(f"stdout: {e.stdout}", file=sys.stderr)
        print(f"stderr: {e.stderr}", file=sys.stderr)
        return None

def main():
    # Load attempts
    attempts_file = '/tmp/pvsnp_attempts.json'
    with open(attempts_file, 'r') as f:
        attempts = json.load(f)

    print(f"Loaded {len(attempts)} attempts")

    # Confirm before creating
    print("\nThis will create GitHub issues for all attempts.")
    print("Do you want to:")
    print("1. Dry run (just print what would be created)")
    print("2. Create a few test issues (first 3)")
    print("3. Create ALL issues (not recommended without testing first)")
    print("4. Cancel")

    choice = input("\nEnter choice (1-4): ").strip()

    if choice == '1':
        print("\n=== DRY RUN ===")
        for attempt in attempts[:10]:  # Show first 10 as sample
            create_issue(attempt, dry_run=True)
        print(f"\n...and {len(attempts) - 10} more issues would be created")

    elif choice == '2':
        print("\n=== Creating first 3 issues ===")
        for attempt in attempts[:3]:
            create_issue(attempt, dry_run=False)
        print("\nDone! Check the issues and re-run with option 3 if they look good.")

    elif choice == '3':
        confirm = input(f"\nAre you SURE you want to create {len(attempts)} issues? (yes/no): ")
        if confirm.lower() == 'yes':
            print("\n=== Creating ALL issues ===")
            created_count = 0
            for i, attempt in enumerate(attempts, 1):
                print(f"[{i}/{len(attempts)}] ", end='')
                result = create_issue(attempt, dry_run=False)
                if result:
                    created_count += 1
            print(f"\nCompleted! Created {created_count} issues.")
        else:
            print("Cancelled.")
    else:
        print("Cancelled.")

if __name__ == '__main__':
    main()
