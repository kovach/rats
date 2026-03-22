import { createServer } from 'http';
import { readFile, writeFile } from 'fs/promises';
import { WebSocketServer } from 'ws';
import { resolve, extname } from 'path';
import { fileURLToPath } from 'url';
import { dirname } from 'path';

const __dirname = dirname(fileURLToPath(import.meta.url));
const sourceFile = process.argv[2];
if (!sourceFile) { console.error('Usage: node server.js <source-file>'); process.exit(1); }

const MIME = { '.html': 'text/html', '.js': 'application/javascript', '.json': 'application/json' };

const server = createServer(async (req, res) => {
  const path = req.url === '/' ? '/index.html' : req.url;
  const file = resolve(__dirname, '.' + path);
  try {
    const data = await readFile(file);
    res.writeHead(200, { 'Content-Type': MIME[extname(file)] ?? 'text/plain' });
    res.end(data);
  } catch { res.writeHead(404); res.end('Not found'); }
});

const wss = new WebSocketServer({ server });
wss.on('connection', async ws => {
  try { ws.send(await readFile(sourceFile, 'utf8')); } catch { ws.send(''); }
  ws.on('message', async data => {
    await writeFile(sourceFile, data.toString());
    console.log(`saved ${sourceFile}`);
  });
});

server.listen(process.env.PORT ?? 3000, () => console.log(`http://localhost:${process.env.PORT ?? 3000}`));
