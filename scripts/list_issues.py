#!/usr/bin/env python3
"""List GitHub issues (not pull requests) for a repository.

The GitHub issues endpoint returns issues and pull requests together, so every
page is fetched by following the ``Link: rel="next"`` header before pull
requests are filtered out. Any transport, HTTP, JSON, or schema error aborts
the listing with exit status 1; an unavailable response is never reported as
an empty list.

Authentication is optional. When ``GH_TOKEN`` or ``GITHUB_TOKEN`` is set, it is
sent in the ``Authorization`` header and never printed.

Exit status: 0 on a successful listing, 1 when the listing could not be
fetched or validated, 2 for invalid command-line arguments.
"""

import argparse
import datetime
import http.client
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

DEFAULT_REPO = 'konard/p-vs-np'
DEFAULT_API_URL = 'https://api.github.com'
PER_PAGE = 100
TOKEN_VARIABLES = ('GH_TOKEN', 'GITHUB_TOKEN')
LINK_NEXT = re.compile(r'<([^>]+)>\s*;\s*rel="next"')


class ListingError(Exception):
    """The issue listing could not be fetched or validated."""


def auth_token(environ=os.environ):
    for name in TOKEN_VARIABLES:
        value = environ.get(name, '').strip()
        if value:
            return value
    return None


def next_link(header):
    if not header:
        return None
    match = LINK_NEXT.search(header)
    return match.group(1) if match else None


def same_origin(first, second):
    a, b = urllib.parse.urlsplit(first), urllib.parse.urlsplit(second)
    return (a.scheme, a.netloc) == (b.scheme, b.netloc)


def http_error_message(error):
    try:
        body = json.loads(error.read().decode('utf-8', 'replace'))
        detail = body.get('message') if isinstance(body, dict) else None
    except (ValueError, OSError):
        detail = None
    message = f'HTTP {error.code}'
    if detail:
        message += f': {detail}'
    headers = error.headers or {}
    if error.code in (403, 429) and headers.get('X-RateLimit-Remaining') == '0':
        reset = headers.get('X-RateLimit-Reset', '')
        if reset.isdigit():
            when = datetime.datetime.fromtimestamp(int(reset), datetime.timezone.utc)
            message += f' (rate limit exhausted; resets at {when:%Y-%m-%dT%H:%M:%SZ})'
        else:
            message += ' (rate limit exhausted)'
        if not auth_token():
            message += '; set GH_TOKEN or GITHUB_TOKEN for a higher limit'
    return message


def fetch_page(url, token, timeout):
    headers = {
        'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28',
        'User-Agent': 'p-vs-np-list-issues',
    }
    if token:
        headers['Authorization'] = f'Bearer {token}'
    request = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            body = response.read()
            link = response.headers.get('Link')
    except urllib.error.HTTPError as error:
        raise ListingError(f'{http_error_message(error)} for {url}') from None
    except (urllib.error.URLError, OSError, http.client.HTTPException) as error:
        reason = getattr(error, 'reason', error)
        raise ListingError(f'request failed for {url}: {reason}') from None
    try:
        data = json.loads(body)
    except ValueError as error:
        raise ListingError(f'invalid JSON from {url}: {error}') from None
    if not isinstance(data, list):
        raise ListingError(f'expected a JSON array from {url}, got {type(data).__name__}')
    return data, next_link(link)


def validate_item(item, url):
    if not isinstance(item, dict):
        raise ListingError(f'expected an object in the array from {url}')
    required = {
        'number': int, 'title': str, 'state': str,
        'created_at': str, 'html_url': str,
    }
    for key, kind in required.items():
        if not isinstance(item.get(key), kind) or isinstance(item.get(key), bool):
            raise ListingError(f'item from {url} has missing or invalid "{key}"')
    if item['state'] not in ('open', 'closed'):
        raise ListingError(f'item #{item["number"]} from {url} has unknown state {item["state"]!r}')
    labels = item.get('labels', [])
    if not isinstance(labels, list) or not all(
            isinstance(label, dict) and isinstance(label.get('name'), str) for label in labels):
        raise ListingError(f'item #{item["number"]} from {url} has invalid "labels"')


def fetch_issues(repo, state='all', limit=None, api_url=DEFAULT_API_URL,
                 token=None, timeout=30):
    """Return ``(issues, complete)`` for the most recently created issues.

    ``complete`` is False only when ``limit`` stopped the listing before the
    last page was reached.
    """
    query = urllib.parse.urlencode({
        'state': state, 'sort': 'created', 'direction': 'desc', 'per_page': PER_PAGE,
    })
    url = f'{api_url.rstrip("/")}/repos/{repo}/issues?{query}'
    issues, seen = [], set()
    while url:
        if url in seen:
            raise ListingError(f'pagination loop at {url}')
        seen.add(url)
        page, following = fetch_page(url, token, timeout)
        for item in page:
            validate_item(item, url)
            if 'pull_request' in item:
                continue
            if limit is not None and len(issues) == limit:
                return issues, False
            issues.append(item)
        if following and not same_origin(following, api_url):
            raise ListingError(f'refusing to follow pagination link to another host: {following}')
        url = following
    return issues, True


def format_issue(issue):
    lines = [
        f'Issue #{issue["number"]}: {issue["title"]}',
        f'  State: {issue["state"]}',
        f'  Created: {issue["created_at"][:10]}',
        f'  URL: {issue["html_url"]}',
    ]
    labels = ', '.join(label['name'] for label in issue.get('labels', []))
    if labels:
        lines.append(f'  Labels: {labels}')
    return '\n'.join(lines)


def render(repo, state, issues, complete, limit, fetched_at):
    scope = 'complete' if complete else f'partial: limited to the {limit} most recently created'
    lines = [
        f'Issues for {repo} (state={state}, fetched {fetched_at:%Y-%m-%dT%H:%M:%SZ}, {scope})',
    ]
    states = ('open', 'closed') if state == 'all' else (state,)
    for section in states:
        selected = [issue for issue in issues if issue['state'] == section]
        lines += ['', '=' * 42, f'{section.upper()} ISSUES ({len(selected)}):', '']
        if not selected:
            lines.append(f'  No {section} issues found.')
        for issue in selected:
            lines += [format_issue(issue), '']
    return '\n'.join(lines).rstrip() + '\n'


def positive_int(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError('must be at least 1')
    return number


def parse_args(argv):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('--repo', default=DEFAULT_REPO,
                        help=f'repository as OWNER/NAME (default: {DEFAULT_REPO})')
    parser.add_argument('--state', choices=('open', 'closed', 'all'), default='all',
                        help='issue state to list (default: all)')
    parser.add_argument('--limit', type=positive_int,
                        help='list only the N most recently created issues (default: all)')
    parser.add_argument('--api-url', default=DEFAULT_API_URL,
                        help=f'GitHub API base URL (default: {DEFAULT_API_URL})')
    parser.add_argument('--timeout', type=float, default=30,
                        help='per-request timeout in seconds (default: 30)')
    args = parser.parse_args(argv)
    if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', args.repo):
        parser.error(f'--repo must be OWNER/NAME, got {args.repo!r}')
    return args


def main(argv=None):
    args = parse_args(argv)
    try:
        issues, complete = fetch_issues(
            args.repo, args.state, args.limit, args.api_url, auth_token(), args.timeout)
    except ListingError as error:
        print(f'error: {error}', file=sys.stderr)
        return 1
    fetched_at = datetime.datetime.now(datetime.timezone.utc)
    sys.stdout.write(render(args.repo, args.state, issues, complete, args.limit, fetched_at))
    return 0


if __name__ == '__main__':
    sys.exit(main())
