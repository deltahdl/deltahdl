#include "parser/precompiled_library.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

namespace delta {

namespace {

// Tool-specific magic identifying our precompiled-library archive.
// The format is intentionally simple: a fixed 8-byte header followed
// by zero or more chunks, each storing one Save call's library tag and
// source bytes with little-endian length prefixes.
constexpr char kMagic[] = "DPLIB001";
constexpr std::streamsize kMagicLen = 8;

void WriteU32(std::ofstream& os, uint32_t v) {
  unsigned char buf[4] = {
      static_cast<unsigned char>(v),
      static_cast<unsigned char>(v >> 8),
      static_cast<unsigned char>(v >> 16),
      static_cast<unsigned char>(v >> 24),
  };
  os.write(reinterpret_cast<const char*>(buf), 4);
}

bool ReadU32(std::ifstream& is, uint32_t& v) {
  unsigned char buf[4];
  if (!is.read(reinterpret_cast<char*>(buf), 4)) return false;
  v = static_cast<uint32_t>(buf[0]) |
      (static_cast<uint32_t>(buf[1]) << 8) |
      (static_cast<uint32_t>(buf[2]) << 16) |
      (static_cast<uint32_t>(buf[3]) << 24);
  return true;
}

bool ReadBytes(std::ifstream& is, std::string& out, uint32_t n) {
  out.resize(n);
  if (n == 0) return true;
  return static_cast<bool>(is.read(out.data(), n));
}

// Run the parser on `source` with a throwaway diagnostics engine; the
// §33.5.3 mandate "shall be parsed and compiled into the library"
// means we must reject ill-formed source at Save time rather than let
// it silently accumulate on disk.
bool ParsesCleanly(std::string_view source) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  uint32_t fid = mgr.AddFile("<precompile>", std::string(source));
  Lexer lex(mgr.FileContent(fid), fid, diag);
  Parser parser(lex, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// Stamp every cell-kind element of `cu` with `library`, mirroring the
// §33.3.3 tagging step that LibraryMap performs on freshly parsed
// source.  The library identifier is stored in `arena` so its lifetime
// matches the AST nodes that point at it.
void TagCells(CompilationUnit& cu, std::string_view library, Arena& arena) {
  auto* buf = static_cast<char*>(arena.Allocate(library.size(), 1));
  std::copy_n(library.data(), library.size(), buf);
  std::string_view view{buf, library.size()};
  for (auto* m : cu.modules) m->library = view;
  for (auto* i : cu.interfaces) i->library = view;
  for (auto* p : cu.programs) p->library = view;
  for (auto* u : cu.udps) u->library = view;
  for (auto* p : cu.packages) p->library = view;
  for (auto* c : cu.configs) c->library = view;
}

void AppendCells(CompilationUnit& target, const CompilationUnit& src) {
  target.modules.insert(target.modules.end(), src.modules.begin(),
                        src.modules.end());
  target.interfaces.insert(target.interfaces.end(), src.interfaces.begin(),
                           src.interfaces.end());
  target.programs.insert(target.programs.end(), src.programs.begin(),
                         src.programs.end());
  target.udps.insert(target.udps.end(), src.udps.begin(), src.udps.end());
  target.packages.insert(target.packages.end(), src.packages.begin(),
                         src.packages.end());
  target.configs.insert(target.configs.end(), src.configs.begin(),
                        src.configs.end());
}

}  // namespace

bool PrecompiledLibrary::Save(std::string_view source,
                              std::string_view library,
                              const std::filesystem::path& path) {
  if (!ParsesCleanly(source)) return false;

  std::error_code ec;
  bool first = !std::filesystem::exists(path, ec) ||
               std::filesystem::file_size(path, ec) == 0;

  std::ofstream os(path, std::ios::binary | std::ios::app);
  if (!os.good()) return false;
  if (first) os.write(kMagic, kMagicLen);

  WriteU32(os, static_cast<uint32_t>(library.size()));
  if (!library.empty()) {
    os.write(library.data(), static_cast<std::streamsize>(library.size()));
  }
  WriteU32(os, static_cast<uint32_t>(source.size()));
  if (!source.empty()) {
    os.write(source.data(), static_cast<std::streamsize>(source.size()));
  }
  return os.good();
}

bool PrecompiledLibrary::Load(const std::filesystem::path& path,
                              CompilationUnit& target, SourceManager& mgr,
                              Arena& arena, DiagEngine& diag) {
  std::ifstream is(path, std::ios::binary);
  if (!is.good()) return false;

  char magic[kMagicLen];
  if (!is.read(magic, kMagicLen)) return false;
  if (std::memcmp(magic, kMagic, kMagicLen) != 0) return false;

  while (true) {
    if (is.peek() == EOF) break;
    uint32_t lib_len = 0;
    if (!ReadU32(is, lib_len)) return false;
    std::string library;
    if (!ReadBytes(is, library, lib_len)) return false;

    uint32_t src_len = 0;
    if (!ReadU32(is, src_len)) return false;
    std::string source;
    if (!ReadBytes(is, source, src_len)) return false;

    uint32_t fid = mgr.AddFile(path.string(), std::move(source));
    Lexer lex(mgr.FileContent(fid), fid, diag);
    Parser parser(lex, arena, diag);
    auto* cu = parser.Parse();
    if (cu == nullptr || diag.HasErrors()) return false;

    TagCells(*cu, library, arena);
    AppendCells(target, *cu);
  }
  return true;
}

}  // namespace delta
