/*
 * targz.mjs — dependency-free tar + gzip (dynamic-Huffman DEFLATE) in one ES6 file.
 *
 * This file is a line-by-line transcription of the Lean 4 model in TarGz/,
 * where the algorithms are proved correct (headline theorem:
 * `extract (create files) = some files`). Each function is annotated with the
 * Lean definition it mirrors. Documented divergences (bit accumulator instead
 * of List Bool, typed-array tables instead of association lists) are enforced
 * by byte-identical differential tests against the Lean executable.
 *
 * The core is pure Uint8Array code with zero imports — it runs in a browser.
 * The CLI at the bottom activates only under Node and loads node:fs lazily.
 *
 *   node targz.mjs c out.tar.gz <files...>   create
 *   node targz.mjs x archive.tar.gz [-C dir] extract
 *   node targz.mjs t archive.tar.gz          list
 */

/* ============================== Core (pure) ============================== */
/* Placeholder — filled in module order: Crc32, Huffman, Lz77, Deflate, Gzip, Tar. */

// Lean: TarGz.Crc32.crc32
export function crc32(_bytes) {
  throw new Error('not implemented yet');
}

// Lean: TarGz.Gzip.gzip / gunzip
export function gzip(_bytes) { throw new Error('not implemented yet'); }
export function gunzip(_bytes) { throw new Error('not implemented yet'); }

// Lean: TarGz.Deflate.deflate / inflate
export function deflate(_bytes) { throw new Error('not implemented yet'); }
export function inflate(_bytes) { throw new Error('not implemented yet'); }

// Lean: TarGz.Correctness.create / extract
// entries: [{ name: string, data: Uint8Array }]
export function create(_entries) { throw new Error('not implemented yet'); }
export function extract(_bytes) { throw new Error('not implemented yet'); }

/* ================================= CLI ================================== */

const USAGE = `usage:
  node targz.mjs c <out.tar.gz> <files...>    create archive
  node targz.mjs x <archive.tar.gz> [-C dir]  extract archive
  node targz.mjs t <archive.tar.gz>           list contents`;

async function runCli() {
  const [cmd, ...rest] = process.argv.slice(2);
  if (!cmd || !['c', 'x', 't'].includes(cmd) || rest.length === 0) {
    console.error(USAGE);
    process.exit(cmd === undefined ? 0 : 1);
  }
  console.error('CLI not implemented yet');
  process.exit(1);
}

// Node-only entry detection; in a browser this whole block is inert.
if (typeof process !== 'undefined' && process.versions?.node && process.argv?.[1]) {
  const { pathToFileURL } = await import('node:url');
  if (import.meta.url === pathToFileURL(process.argv[1]).href) {
    await runCli();
  }
}
