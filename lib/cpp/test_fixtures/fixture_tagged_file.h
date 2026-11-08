#pragma once

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_diagnosed.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

inline std::string ReadFileText(const std::filesystem::path& path) {
  std::ifstream ifs(path);
  std::ostringstream buf;
  buf << ifs.rdbuf();
  return buf.str();
}

struct TaggedFile {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
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
    diagnosed.Record(path.string());
  }

  std::string_view Library() const {
    if (unit == nullptr || unit->modules.size() != 1u) return {};
    return unit->modules[0]->library;
  }
};
