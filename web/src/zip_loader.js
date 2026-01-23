export async function loadZipFile(file) {
  const buffer = await file.arrayBuffer();
  return buildRunsFromFiles(await unzipBuffer(buffer));
}

export async function loadFolderFiles(fileList) {
  const files = {};
  const entries = [];
  for (const file of fileList) {
    const path = file.webkitRelativePath || file.name;
    const buffer = await file.arrayBuffer();
    files[path] = new Uint8Array(buffer);
    entries.push({ path, size: file.size });
  }
  return buildRunsFromFiles({ files, entries });
}

async function unzipBuffer(buffer) {
  const data = new Uint8Array(buffer);
  const view = new DataView(buffer);
  const eocdOffset = findEocdOffset(data);
  if (eocdOffset < 0) {
    throw new Error("Invalid ZIP file.");
  }

  const centralDirOffset = view.getUint32(eocdOffset + 16, true);
  const centralDirSize = view.getUint32(eocdOffset + 12, true);
  let cursor = centralDirOffset;
  const files = {};
  const entries = [];

  while (cursor < centralDirOffset + centralDirSize) {
    const signature = view.getUint32(cursor, true);
    if (signature !== 0x02014b50) break;
    const compMethod = view.getUint16(cursor + 10, true);
    const compSize = view.getUint32(cursor + 20, true);
    const nameLen = view.getUint16(cursor + 28, true);
    const extraLen = view.getUint16(cursor + 30, true);
    const commentLen = view.getUint16(cursor + 32, true);
    const localHeaderOffset = view.getUint32(cursor + 42, true);
    const nameBytes = data.slice(cursor + 46, cursor + 46 + nameLen);
    const name = new TextDecoder().decode(nameBytes);

    if (!name.endsWith("/")) {
      const localSignature = view.getUint32(localHeaderOffset, true);
      if (localSignature !== 0x04034b50) {
        throw new Error("Invalid local file header.");
      }
      const localNameLen = view.getUint16(localHeaderOffset + 26, true);
      const localExtraLen = view.getUint16(localHeaderOffset + 28, true);
      const dataStart = localHeaderOffset + 30 + localNameLen + localExtraLen;
      const compressed = data.slice(dataStart, dataStart + compSize);
      const content = await decompress(compMethod, compressed);
      files[name] = content;
      entries.push({ path: name, size: content.byteLength });
    }

    cursor += 46 + nameLen + extraLen + commentLen;
  }

  return { files, entries };
}

async function decompress(method, data) {
  if (method === 0) {
    return data;
  }
  if (method === 8) {
    const stream = new DecompressionStream("deflate-raw");
    const blob = new Blob([data]);
    const decompressed = await new Response(blob.stream().pipeThrough(stream)).arrayBuffer();
    return new Uint8Array(decompressed);
  }
  throw new Error(`Unsupported compression method: ${method}`);
}

function findEocdOffset(data) {
  for (let i = data.length - 22; i >= Math.max(0, data.length - 65557); i -= 1) {
    if (
      data[i] === 0x50 &&
      data[i + 1] === 0x4b &&
      data[i + 2] === 0x05 &&
      data[i + 3] === 0x06
    ) {
      return i;
    }
  }
  return -1;
}

function buildRunsFromFiles({ files, entries }) {
  const required = ["telemetry.json", "sophia_audit.json", "sophia_plan.json"];
  const runIndex = new Map();

  entries.forEach((entry) => {
    const parts = entry.path.split("/");
    const root = parts.length > 1 ? parts[0] : "(root)";
    if (!runIndex.has(root)) {
      runIndex.set(root, { files: [], sizes: {}, rootPath: root });
    }
    const run = runIndex.get(root);
    run.files.push(entry.path);
    run.sizes[entry.path] = entry.size;
  });

  const runs = [];
  for (const [root, run] of runIndex.entries()) {
    const hasRequired = required.every((file) =>
      run.files.some((path) => path.endsWith(`${root === "(root)" ? "" : root + "/"}${file}`))
    );
    if (hasRequired) {
      runs.push({ name: root, rootPath: root, files: run.files, sizes: run.sizes });
    }
  }

  if (runs.length === 0) {
    runs.push({ name: "(root)", rootPath: "(root)", files: Object.keys(files), sizes: {} });
  }

  return { files, entries, runs };
}
