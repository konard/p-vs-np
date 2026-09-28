"""Regression tests for the GitHub issue listing script.

Each test serves canned GitHub API responses from a local HTTP server and runs
the script as a subprocess, so exit status, stdout and stderr are all checked
without network access or credentials.
"""

import http.server
import json
import os
import socket
import subprocess
import sys
import threading
import unittest
from pathlib import Path

from scripts.list_issues import next_link

SCRIPT = Path(__file__).resolve().parent / 'list_issues.py'
FIRST = '/repos/owner/repo/issues?state=all&sort=created&direction=desc&per_page=100'
TOKEN = 'ghp_secret_test_token_value'


def issue(number, state='open', labels=()):
    return {
        'number': number,
        'title': f'Issue title {number}',
        'state': state,
        'created_at': '2026-09-28T12:00:00Z',
        'html_url': f'https://github.com/owner/repo/issues/{number}',
        'labels': [{'name': name} for name in labels],
    }


def pull(number, state='open'):
    return dict(issue(number, state), pull_request={'url': 'https://example.invalid'})


class FakeGitHub(http.server.ThreadingHTTPServer):
    """Serves ``routes[path] = (status, headers, body)`` and records requests."""

    def __init__(self):
        super().__init__(('127.0.0.1', 0), Handler)
        self.routes = {}
        self.requests = []
        self.base = f'http://127.0.0.1:{self.server_address[1]}'

    def page(self, path, items, following=None, status=200, headers=None):
        headers = dict(headers or {})
        if following:
            headers['Link'] = f'<{self.base}{following}>; rel="next", <{self.base}/last>; rel="last"'
        body = items if isinstance(items, bytes) else json.dumps(items).encode()
        self.routes[path] = (status, headers, body)


class Handler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        self.server.requests.append((self.path, self.headers.get('Authorization')))
        status, headers, body = self.server.routes.get(
            self.path, (404, {}, b'{"message": "Not Found"}'))
        self.send_response(status)
        for name, value in headers.items():
            self.send_header(name, value)
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *args):
        pass


class ListIssuesTests(unittest.TestCase):
    def setUp(self):
        self.server = FakeGitHub()
        thread = threading.Thread(target=self.server.serve_forever, args=(0.05,), daemon=True)
        thread.start()
        self.addCleanup(thread.join)
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)

    def run_script(self, *args, api_url=None, token=None):
        env = {key: value for key, value in os.environ.items()
               if key not in ('GH_TOKEN', 'GITHUB_TOKEN')}
        if token:
            env['GH_TOKEN'] = token
        return subprocess.run(
            [sys.executable, str(SCRIPT), '--repo', 'owner/repo',
             '--api-url', api_url or self.server.base, '--timeout', '5', *args],
            capture_output=True, text=True, env=env, timeout=30)

    def assert_failed(self, result, *fragments):
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(result.stdout, '')
        for fragment in fragments:
            self.assertIn(fragment, result.stderr)

    def test_follows_every_page_before_filtering_pull_requests(self):
        self.server.page(FIRST, [pull(9), issue(8, labels=['bug', 'help']), pull(7)], '/p2')
        self.server.page('/p2', [issue(6), pull(5)], '/p3')
        self.server.page('/p3', [issue(4, 'closed')])
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([path for path, _ in self.server.requests], [FIRST, '/p2', '/p3'])
        self.assertIn(', complete)', result.stdout)
        self.assertIn('OPEN ISSUES (2):', result.stdout)
        self.assertIn('CLOSED ISSUES (1):', result.stdout)
        for number in (8, 6, 4):
            self.assertIn(f'Issue #{number}: Issue title {number}', result.stdout)
        for number in (9, 7, 5):
            self.assertNotIn(f'#{number}:', result.stdout)
        self.assertIn('  Labels: bug, help', result.stdout)
        self.assertNotIn('\033', result.stdout)

    def test_pull_request_only_first_page_does_not_hide_older_issues(self):
        self.server.page(FIRST, [pull(number) for number in range(200, 100, -1)], '/p2')
        self.server.page('/p2', [issue(3), issue(2, 'closed')])
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('No open issues found', result.stdout)
        self.assertIn('Issue #3:', result.stdout)
        self.assertIn('Issue #2:', result.stdout)

    def test_empty_repository_is_a_successful_empty_listing(self):
        self.server.page(FIRST, [])
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('No open issues found.', result.stdout)
        self.assertIn('No closed issues found.', result.stdout)
        self.assertEqual(result.stderr, '')

    def test_single_state_lists_one_section(self):
        path = FIRST.replace('state=all', 'state=open')
        self.server.page(path, [issue(1)])
        result = self.run_script('--state', 'open')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('OPEN ISSUES (1):', result.stdout)
        self.assertNotIn('CLOSED ISSUES', result.stdout)

    def test_rate_limit_fails_with_reset_time(self):
        self.server.page(FIRST, {'message': 'API rate limit exceeded for 127.0.0.1.'}, status=403,
                         headers={'X-RateLimit-Remaining': '0', 'X-RateLimit-Reset': '1790610000'})
        result = self.run_script()
        self.assert_failed(result, 'HTTP 403: API rate limit exceeded',
                           'resets at 2026-09-28T15:40:00Z', 'set GH_TOKEN or GITHUB_TOKEN')

    def test_secondary_rate_limit_status_429_fails(self):
        self.server.page(FIRST, {'message': 'secondary rate limit'}, status=429,
                         headers={'X-RateLimit-Remaining': '0'})
        self.assert_failed(self.run_script(), 'HTTP 429', 'rate limit exhausted')

    def test_http_error_fails(self):
        self.server.page(FIRST, b'<html>Bad gateway</html>', status=502)
        self.assert_failed(self.run_script(), 'HTTP 502')

    def test_error_on_later_page_prints_no_partial_listing(self):
        self.server.page(FIRST, [issue(5)], '/p2')
        self.server.page('/p2', {'message': 'Server Error'}, status=500)
        self.assert_failed(self.run_script(), 'HTTP 500: Server Error', '/p2')

    def test_missing_repository_fails(self):
        self.assert_failed(self.run_script(), 'HTTP 404: Not Found')

    def test_invalid_json_fails(self):
        self.server.page(FIRST, b'[{"number": 1,')
        self.assert_failed(self.run_script(), 'invalid JSON')

    def test_error_object_with_success_status_fails(self):
        # The reproduction from issue #612: a JSON error object instead of an array.
        self.server.page(FIRST, {'message': 'API rate limit exceeded'})
        self.assert_failed(self.run_script(), 'expected a JSON array', 'got dict')

    def test_item_schema_errors_fail(self):
        bad_items = {
            'missing title': dict(issue(1), title=None),
            'boolean number': dict(issue(1), number=True),
            'unknown state': issue(1, state='merged'),
            'bad labels': dict(issue(1), labels=['bug']),
            'non-object': 'issue',
        }
        for name, item in bad_items.items():
            with self.subTest(name):
                self.server.page(FIRST, [item])
                self.assert_failed(self.run_script(), 'error:')

    def test_transport_failure_fails(self):
        with socket.socket() as probe:
            probe.bind(('127.0.0.1', 0))
            port = probe.getsockname()[1]
        self.assert_failed(self.run_script(api_url=f'http://127.0.0.1:{port}'), 'request failed')

    def test_token_is_sent_but_never_printed(self):
        self.server.page(FIRST, [issue(1)], '/p2')
        self.server.page('/p2', {'message': 'Bad credentials'}, status=401)
        result = self.run_script(token=TOKEN)
        self.assert_failed(result, 'HTTP 401: Bad credentials')
        self.assertNotIn(TOKEN, result.stderr)
        self.assertEqual([auth for _, auth in self.server.requests], [f'Bearer {TOKEN}'] * 2)

    def test_unauthenticated_requests_send_no_authorization(self):
        self.server.page(FIRST, [issue(1)])
        self.assertEqual(self.run_script().returncode, 0)
        self.assertEqual(self.server.requests, [(FIRST, None)])

    def test_cross_origin_pagination_link_is_refused(self):
        self.server.routes[FIRST] = (200, {'Link': '<https://evil.invalid/p2>; rel="next"'},
                                     json.dumps([issue(1)]).encode())
        result = self.run_script(token=TOKEN)
        self.assert_failed(result, 'refusing to follow pagination link')
        self.assertEqual(len(self.server.requests), 1)

    def test_pagination_loop_fails(self):
        self.server.page(FIRST, [issue(1)], '/p2')
        self.server.page('/p2', [issue(2)], FIRST)
        self.assert_failed(self.run_script(), 'pagination loop')

    def test_limit_marks_listing_partial_and_stops_fetching(self):
        self.server.page(FIRST, [issue(9), pull(8), issue(7)], '/p2')
        self.server.page('/p2', [issue(6)])
        result = self.run_script('--limit', '1')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('partial: limited to the 1 most recently created', result.stdout)
        self.assertIn('Issue #9:', result.stdout)
        self.assertNotIn('Issue #7:', result.stdout)
        self.assertEqual(len(self.server.requests), 1)

    def test_limit_checks_next_page_before_claiming_partial(self):
        self.server.page(FIRST, [issue(9), pull(8), issue(7)], '/p2')
        self.server.page('/p2', [issue(6)])
        result = self.run_script('--limit', '2')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('partial: limited to the 2 most recently created', result.stdout)
        self.assertIn('Issue #7:', result.stdout)
        self.assertNotIn('Issue #6:', result.stdout)

    def test_limit_covering_all_issues_is_complete(self):
        self.server.page(FIRST, [issue(9), issue(7)])
        result = self.run_script('--limit', '2')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(', complete)', result.stdout)

    def test_invalid_arguments_exit_with_usage_error(self):
        for args in (['--limit', '0'], ['--state', 'merged'], ['--repo', 'not-a-repo']):
            with self.subTest(args=args):
                result = subprocess.run([sys.executable, str(SCRIPT), *args],
                                        capture_output=True, text=True, timeout=30)
                self.assertEqual(result.returncode, 2)
        self.assertEqual(self.server.requests, [])


class NextLinkTests(unittest.TestCase):
    def test_parses_next_among_other_relations(self):
        header = ('<https://api.github.com/x?page=1>; rel="prev", '
                  '<https://api.github.com/x?page=3>; rel="next", '
                  '<https://api.github.com/x?page=9>; rel="last"')
        self.assertEqual(next_link(header), 'https://api.github.com/x?page=3')

    def test_last_page_has_no_next(self):
        self.assertIsNone(next_link('<https://api.github.com/x?page=1>; rel="first"'))
        self.assertIsNone(next_link(None))


if __name__ == '__main__':
    unittest.main()
