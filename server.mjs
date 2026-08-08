import { spawn } from "node:child_process";
import { createReadStream } from "node:fs";
import { stat } from "node:fs/promises";
import { createServer } from "node:http";
import { extname, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(fileURLToPath(new URL(".", import.meta.url)));
const host = process.env.HOST || "127.0.0.1";
const port = Number(process.env.PORT || 4174);
const shouldOpen = !process.argv.includes("--no-open");

const mimeTypes = {
    ".css": "text/css; charset=utf-8",
    ".html": "text/html; charset=utf-8",
    ".ico": "image/x-icon",
    ".jpeg": "image/jpeg",
    ".jpg": "image/jpeg",
    ".js": "text/javascript; charset=utf-8",
    ".json": "application/json; charset=utf-8",
    ".map": "application/json; charset=utf-8",
    ".png": "image/png",
    ".svg": "image/svg+xml",
    ".txt": "text/plain; charset=utf-8",
    ".webp": "image/webp",
    ".woff": "font/woff",
    ".woff2": "font/woff2"
};

function openBrowser(url) {
    const command = process.platform === "win32"
        ? ["cmd.exe", ["/c", "start", "", url]]
        : process.platform === "darwin"
            ? ["open", [url]]
            : ["xdg-open", [url]];

    try {
        spawn(command[0], command[1], { detached: true, stdio: "ignore" }).unref();
    } catch {
        // The URL is printed below even when no desktop opener is available.
    }
}

const server = createServer(async (request, response) => {
    try {
        const url = new URL(request.url || "/", `http://${request.headers.host || host}`);
        let pathname = decodeURIComponent(url.pathname);
        if (pathname.endsWith("/")) pathname += "index.html";

        const filePath = resolve(root, pathname.replace(/^\/+/, ""));
        if (filePath !== root && !filePath.startsWith(root + sep)) {
            response.writeHead(403, { "Content-Type": "text/plain; charset=utf-8" });
            response.end("Forbidden");
            return;
        }

        const fileInfo = await stat(filePath);
        if (!fileInfo.isFile()) throw new Error("Not a file");

        response.writeHead(200, {
            "Cache-Control": "no-cache",
            "Content-Length": fileInfo.size,
            "Content-Type": mimeTypes[extname(filePath).toLowerCase()] || "application/octet-stream"
        });

        if (request.method === "HEAD") {
            response.end();
            return;
        }
        createReadStream(filePath).pipe(response);
    } catch {
        response.writeHead(404, { "Content-Type": "text/plain; charset=utf-8" });
        response.end("Not found");
    }
});

server.on("error", error => {
    console.error(`Unable to start Deductrium server: ${error.message}`);
    process.exitCode = 1;
});

server.listen(port, host, () => {
    const url = `http://${host}:${port}/`;
    console.log(`Deductrium is running at ${url}`);
    console.log("Press Ctrl+C to stop.");
    if (shouldOpen) openBrowser(url);
});
