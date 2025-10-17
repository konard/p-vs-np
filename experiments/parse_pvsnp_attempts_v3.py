#!/usr/bin/env python3
"""
Parse P vs NP attempts from Woeginger's list - simple regex-based approach.
"""

import re
import json

def parse_html_file(filepath):
    """Parse the HTML file and extract P vs NP attempts."""
    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()

    # Remove HTML tags
    text = re.sub(r'<script[^>]*>.*?</script>', '', content, flags=re.DOTALL)
    text = re.sub(r'<style[^>]*>.*?</style>', '', content, flags=re.DOTALL)
    text = re.sub(r'<[^>]+>', ' ', text)
    text = re.sub(r'\s+', ' ', text)

    attempts = []
    attempt_id = 0

    # Find all [Equal]: and [Not equal]: markers (note: lowercase 'e' in 'equal')
    # Use regex to split by these markers
    pattern = r'\[(Equal|Not equal)\]:\s*'
    parts = re.split(pattern, text)

    # Process parts in pairs (marker, content)
    for i in range(1, len(parts), 2):
        if i + 1 >= len(parts):
            break

        claim_marker = parts[i]
        content = parts[i + 1]

        # Take only first ~500 characters for this attempt
        content = content[:600].strip()

        # Determine claim
        claim = "P=NP" if claim_marker == "Equal" else "P≠NP"

        # Skip if content is too short (likely junk)
        if len(content.strip()) < 20:
            continue

        # Extract year
        year_match = re.search(r'\b(19\d{2}|20\d{2})(?:/\d{2})?\b', content)
        year = year_match.group(1) if year_match else "Unknown"

        # Extract author - try multiple patterns
        author = "Unknown"

        # Pattern 1: "In YEAR Author" or "In YEAR/YY Author"
        # This captures names like "Ted Swart", "Anatoly D. Plotnikov", etc.
        m1 = re.search(r'In\s+(?:19\d{2}|20\d{2})(?:/\d{2})?,?\s+([A-Z][a-zA-Z]+(?:\s+[A-Z]\.?\s*)?[A-Z][a-zA-Z]+(?:\s+[A-Z][a-zA-Z]+)?)', content)
        if m1:
            author = m1.group(1).strip()
            # Remove trailing words that are not part of name
            author = re.sub(r'\s+(wrote|proved|established|designed|constructed|showed|claimed|from|of|at).*$', '', author, flags=re.IGNORECASE)

        # Pattern 2: "Author (University)" or "Author proved"
        if author == "Unknown":
            m2 = re.search(r'\b([A-Z][a-z]+(?:\s+[A-Z]\.?\s*)?[A-Z][a-z]+(?:\s+[A-Z][a-z]+)?)\s+(?:\(|proved|established|wrote|designed|constructed|showed|claimed)', content)
            if m2:
                author = m2.group(1).strip()

        # Pattern 3: First capitalized name before year
        if author == "Unknown" and year_match:
            before_year = content[:year_match.start()]
            m3 = re.search(r'([A-Z][a-z]+(?:\s+[A-Z]\.?\s*)?[A-Z][a-z]+(?:\s+[A-Z][a-z]+)?)\s*$', before_year)
            if m3:
                author = m3.group(1).strip()

        # Clean author name
        author = re.sub(r'\s+', ' ', author)
        # Remove words that got captured but aren't names
        author = re.sub(r'^(In|The|Here|Around)\s+', '', author, flags=re.IGNORECASE)
        author = author[:80]

        # Take first sentence or ~200 chars as description
        desc_match = re.search(r'^(.{10,250}?\.)', content)
        description = desc_match.group(1) if desc_match else content[:200]

        attempt_id += 1
        attempts.append({
            "id": attempt_id,
            "author": author,
            "year": year,
            "claim": claim,
            "description": description.strip()
        })

    return attempts

def main():
    attempts = parse_html_file('/tmp/pvsnp_attempts.html')

    # Save to JSON
    output_file = '/tmp/pvsnp_attempts.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(attempts, f, indent=2, ensure_ascii=False)

    print(f"Extracted {len(attempts)} attempts")
    print(f"Saved to {output_file}")

    # Count by claim
    p_eq_np = sum(1 for a in attempts if a['claim'] == 'P=NP')
    p_neq_np = sum(1 for a in attempts if a['claim'] == 'P≠NP')
    print(f"\nP=NP attempts: {p_eq_np}")
    print(f"P≠NP attempts: {p_neq_np}")

    # Print first 10 as sample
    print("\nFirst 10 attempts:")
    for attempt in attempts[:10]:
        print(f"  {attempt['id']}. {attempt['author']} ({attempt['year']}) - {attempt['claim']}")

if __name__ == '__main__':
    main()
