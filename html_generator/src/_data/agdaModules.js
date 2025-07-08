import * as fs from "fs";
import * as path from "path";
import { finished } from "stream/promises";
import { WritableStream as ParserStream } from "htmlparser2/WritableStream";

async function getModules(prefix, filename) {
  const allModules = [];
  const visited = new Set();
  const queue = [filename];
  visited.add(filename);
  allModules.push({
    href: filename,
    name: prefix + "README"
  });

  while (queue.length > 0) {
    const currentFile = queue.shift();

    const modules = [];
    let currentModule = null;
    const parserStream = new ParserStream({
      onopentag(name, attributes) {
        if (name === "a" && attributes.class === "Module") {
          currentModule = {
            href: attributes.href,
            name: ""
          };
        }
      },
      ontext(text) {
        if (currentModule !== null) {
          currentModule.name += text;
        }
      },
      onclosetag(name) {
        if (name === "a" && currentModule !== null) {
          modules.push(currentModule);
          currentModule = null;
        }
      }
    });

    const stream = fs.createReadStream(path.join(import.meta.dirname, "../agda", currentFile));
    stream.pipe(parserStream);
    await finished(stream);

    // Add sub-modules to queue for BFS
    for (const module of modules) {
      const subFilename = module.href;
      if (subFilename &&
        fs.existsSync(path.join(import.meta.dirname, "../agda", subFilename)) &&
        subFilename.startsWith(prefix) &&
        !visited.has(subFilename)) {
        visited.add(subFilename);
        queue.push(subFilename);
        allModules.push(module);
      }
    }
  }

  return allModules;
}

function toTrie(modules) {
  const trie = new Map();
  for (const module of modules) {
    let current = trie;
    for (const part of module.name.split(".")) {
      if (part === "All") {
        continue;
      }
      if (!current.has(part)) {
        current.set(part, new Map());
      }
      current = current.get(part);
    }
    current.href = module.href;
    current.name = module.name;
  }
  return trie;
}

export default async function () {
  return toTrie(await getModules("Implicit.", "Implicit.README.html"));
}
