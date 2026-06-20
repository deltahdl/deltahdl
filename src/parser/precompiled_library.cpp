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
  v = static_cast<uint32_t>(buf[0]) | (static_cast<uint32_t>(buf[1]) << 8) |
      (static_cast<uint32_t>(buf[2]) << 16) |
      (static_cast<uint32_t>(buf[3]) << 24);
  return true;
}

bool ReadBytes(std::ifstream& is, std::string& out, uint32_t n) {
  out.resize(n);
  if (n == 0) return true;
  return static_cast<bool>(is.read(out.data(), n));
}

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

// Reads a single (library, source) record header from the stream into the
// provided buffers. Returns false on any read failure.
bool ReadRecord(std::ifstream& is, std::string& library, std::string& source) {
  uint32_t lib_len = 0;
  if (!ReadU32(is, lib_len)) return false;
  if (!ReadBytes(is, library, lib_len)) return false;

  uint32_t src_len = 0;
  if (!ReadU32(is, src_len)) return false;
  if (!ReadBytes(is, source, src_len)) return false;
  return true;
}

// Bundles the destination compilation unit together with the shared parsing
// infrastructure (source manager, arena, diagnostics) that a load pass writes
// into. These travel together through PrecompiledLibrary::Load and LoadRecord.
struct LoadContext {
  CompilationUnit& target;
  SourceManager& mgr;
  Arena& arena;
  DiagEngine& diag;
};

// Parses one record's source into the target compilation unit, tagging cells
// with the record's library name. Returns false on parse failure.
bool LoadRecord(const std::filesystem::path& path, const std::string& library,
                std::string source, LoadContext& ctx) {
  uint32_t fid = ctx.mgr.AddFile(path.string(), std::move(source));
  Lexer lex(ctx.mgr.FileContent(fid), fid, ctx.diag);
  Parser parser(lex, ctx.arena, ctx.diag);
  auto* cu = parser.Parse();
  if (cu == nullptr || ctx.diag.HasErrors()) return false;

  TagCells(*cu, library, ctx.arena);
  AppendCells(ctx.target, *cu);
  return true;
}

}  // namespace

bool PrecompiledLibrary::Save(std::string_view source, std::string_view library,
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

  LoadContext ctx{target, mgr, arena, diag};
  while (true) {
    if (is.peek() == EOF) break;
    std::string library;
    std::string source;
    if (!ReadRecord(is, library, source)) return false;
    if (!LoadRecord(path, std::move(library), std::move(source), ctx)) {
      return false;
    }
  }
  return true;
}

}  // namespace delta
