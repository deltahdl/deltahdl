#pragma once

#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

// The text a file holds, read back off disk, so a test that parses a
// description parses the file a specification resolved to rather than a copy of
// it kept beside the tree.
inline std::string ReadFileText(const std::filesystem::path& path) {
  std::ifstream ifs(path);
  std::ostringstream buf;
  buf << ifs.rdbuf();
  return buf.str();
}

// One source file carried the whole way a compiler carries it: read, lexed,
// parsed, and then tagged through `map`, which writes the cells it describes
// into whichever library the file path resolved to (§33.3).
//
// A test about which library holds a file reads the answer off a parsed cell
// rather than off the map alone, because the tagging is the step that turns a
// path specification into the library a cell lives in.
struct TaggedFile {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;
  CompilationUnit* unit = nullptr;

  TaggedFile(const LibraryMap& map, const std::filesystem::path& path) {
    uint32_t fid = mgr.AddFile(path.string(), ReadFileText(path));
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    unit = parser.Parse();
    if (unit != nullptr && !diag.HasErrors()) {
      map.TagCompilationUnit(*unit, path.string());
    }
  }

  // The library the one cell this file describes was written into, or an empty
  // view where the file did not yield exactly one cell.
  std::string_view Library() const {
    if (unit == nullptr || unit->modules.size() != 1u) return {};
    return unit->modules[0]->library;
  }
};
