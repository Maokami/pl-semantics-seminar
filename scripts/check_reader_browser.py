"""Serve the built chapter and run its DOM regression checks in the runner's Chrome."""
import argparse
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory
from threading import Thread

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'verso/site/html-multi'
CHAPTER = '/chapter-01/index.html'


class ChapterHandler(SimpleHTTPRequestHandler):
    def do_GET(self):
        if self.path == CHAPTER:
            script = (ROOT / 'tests/reader-smoke.js').read_text()
            page = (SITE / CHAPTER.lstrip('/')).read_text().replace('</body>', f'<script>{script}</script></body>')
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('Content-Security-Policy', "default-src 'self' data:; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'")
            self.end_headers()
            self.wfile.write(page.encode())
        else:
            super().do_GET()

    def log_message(self, *args):
        pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--serve', action='store_true', help='Open the printed URL in the local cmux browser')
    args = parser.parse_args()
    with ThreadingHTTPServer(('127.0.0.1', 0), partial(ChapterHandler, directory=SITE)) as server:
        url = f'http://127.0.0.1:{server.server_port}{CHAPTER}#ch01-s4-p-c6ac304e1bff'
        if args.serve:
            print(url, flush=True)
            server.serve_forever()
            return
        Thread(target=server.serve_forever, daemon=True).start()
        with TemporaryDirectory() as profile:
            chrome = shutil.which('google-chrome') or shutil.which('chromium')
            if not chrome:
                raise SystemExit('Chrome is required. On macOS use --serve and cmux browser.')
            result = subprocess.run([chrome, '--headless', '--disable-gpu', '--disable-dev-shm-usage',
                                     '--window-size=390,844', '--user-data-dir=' + profile,
                                     '--virtual-time-budget=5000', '--dump-dom', url],
                                    stdout=subprocess.PIPE, text=True, timeout=45, check=True)
            if 'data-reader-test="passed"' not in result.stdout:
                start = result.stdout.find('<body')
                raise SystemExit('Reader smoke failed: ' + result.stdout[start:result.stdout.find('>', start)+1])
            print('Reader smoke passed')
        server.shutdown()


if __name__ == '__main__':
    main()
