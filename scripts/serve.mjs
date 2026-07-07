// SPDX-FileCopyrightText: 2026 K. S. Ernest (iFire) Lee
// SPDX-License-Identifier: MIT

// Minimal dependency-free static file server for the Playwright suite.
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const port = Number(process.env.PORT ?? 8765);

const TYPES = {
  ".html": "text/html; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
};

http
  .createServer((req, res) => {
    const url = new URL(req.url, "http://localhost");
    let p = path.normalize(path.join(root, url.pathname));
    if (!p.startsWith(root)) {
      res.writeHead(403).end();
      return;
    }
    if (url.pathname === "/") p = path.join(root, "playwright", "index.html");
    fs.readFile(p, (err, data) => {
      if (err) {
        res.writeHead(404).end("not found");
        return;
      }
      res.writeHead(200, { "content-type": TYPES[path.extname(p)] ?? "application/octet-stream" });
      res.end(data);
    });
  })
  .listen(port, () => console.log(`serving ${root} on http://localhost:${port}`));
