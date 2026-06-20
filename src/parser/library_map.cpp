#include "parser/library_map.h"

#include <cstdint>
#include <fstream>
#include <sstream>
#include <system_error>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

namespace delta {

namespace {

std::vector<std::string_view> SplitSegments(std::string_view path,
                                            bool& absolute) {
  absolute = !path.empty() && path.front() == '/';
  std::vector<std::string_view> out;
  size_t i = absolute ? 1 : 0;
  while (i < path.size()) {
    size_t j = path.find('/', i);
    if (j == std::string_view::npos) j = path.size();
    out.push_back(path.substr(i, j - i));
    i = (j == path.size()) ? j : j + 1;
  }
  return out;
}

std::string Join(const std::vector<std::string_view>& segs, bool absolute) {
  std::string out;
  if (absolute) out += '/';
  for (size_t i = 0; i < segs.size(); ++i) {
    if (i > 0) out += '/';
    out.append(segs[i].data(), segs[i].size());
  }
  return out;
}

std::vector<std::string_view> Normalize(
    const std::vector<std::string_view>& segs) {
  std::vector<std::string_view> out;
  for (auto seg : segs) {
    if (seg == ".") continue;
    if (seg == "..") {
      if (!out.empty() && out.back() != ".." && out.back() != "...") {
        out.pop_back();
      } else {
        out.push_back(seg);
      }
      continue;
    }
    out.push_back(seg);
  }
  return out;
}

bool GlobOne(std::string_view pat, std::string_view name) {
  size_t pi = 0, ni = 0;
  size_t star_p = std::string_view::npos;
  size_t star_n = 0;
  while (ni < name.size()) {
    if (pi < pat.size() && (pat[pi] == name[ni] || pat[pi] == '?')) {
      ++pi;
      ++ni;
    } else if (pi < pat.size() && pat[pi] == '*') {
      star_p = pi++;
      star_n = ni;
    } else if (star_p != std::string_view::npos) {
      pi = star_p + 1;
      ni = ++star_n;
    } else {
      return false;
    }
  }
  while (pi < pat.size() && pat[pi] == '*') ++pi;
  return pi == pat.size();
}

enum class SpecKind : std::uint8_t {
  kExplicitFilename = 0,
  kWildcardFilename = 1,
  kDirectory = 2,
};

SpecKind ClassifySpec(std::string_view spec) {
  if (spec.empty()) return SpecKind::kExplicitFilename;
  if (spec.back() == '/') return SpecKind::kDirectory;
  size_t last_slash = spec.rfind('/');
  std::string_view tail = (last_slash == std::string_view::npos)
                              ? spec
                              : spec.substr(last_slash + 1);
  if (tail == "...") return SpecKind::kDirectory;
  bool has_wild = tail.find_first_of("*?") != std::string_view::npos ||
                  tail.find("...") != std::string_view::npos;
  return has_wild ? SpecKind::kWildcardFilename : SpecKind::kExplicitFilename;
}

std::string CellKey(std::string_view library, std::string_view name) {
  std::string key(library);
  key.push_back('\0');
  key.append(name);
  return key;
}

bool GlobMatchSegments(const std::vector<std::string_view>& pat_segs, size_t pi,
                       const std::vector<std::string_view>& path_segs,
                       size_t si) {
  if (pi == pat_segs.size()) return si == path_segs.size();
  if (pat_segs[pi] == "...") {
    for (size_t k = si; k <= path_segs.size(); ++k) {
      if (GlobMatchSegments(pat_segs, pi + 1, path_segs, k)) return true;
    }
    return false;
  }
  if (si == path_segs.size()) return false;
  if (!GlobOne(pat_segs[pi], path_segs[si])) return false;
  return GlobMatchSegments(pat_segs, pi + 1, path_segs, si + 1);
}

bool StackContainsPath(const std::vector<std::filesystem::path>& stack,
                       const std::filesystem::path& canon,
                       std::vector<std::string>* errors) {
  for (const auto& p : stack) {
    if (p == canon) {
      if (errors) {
        errors->push_back("library map cycle including " + canon.string());
      }
      return true;
    }
  }
  return false;
}

bool ReadFileContent(const std::filesystem::path& canon, std::string& content,
                     std::vector<std::string>* errors) {
  std::ifstream ifs(canon);
  if (!ifs.good()) {
    if (errors) {
      errors->push_back("cannot open library map file " + canon.string());
    }
    return false;
  }
  std::ostringstream buf;
  buf << ifs.rdbuf();
  content = buf.str();
  return true;
}

CompilationUnit* ParseLibraryMapContent(const std::filesystem::path& canon,
                                        std::string content, Arena& arena,
                                        std::vector<std::string>* errors) {
  SourceManager mgr;
  DiagEngine diag(mgr);
  uint32_t fid = mgr.AddFile(canon.string(), std::move(content));
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.ParseLibraryText();

  if (diag.HasErrors() || cu == nullptr) {
    if (errors) {
      errors->push_back("parse errors in library map file " + canon.string());
    }
    return nullptr;
  }
  return cu;
}

std::filesystem::path ResolveIncludePath(std::string_view file_path,
                                         const std::filesystem::path& canon) {
  std::filesystem::path inc_path{std::string{file_path}};
  if (inc_path.is_relative()) {
    inc_path = canon.parent_path() / inc_path;
  }
  return inc_path;
}

}  // namespace

std::string LibraryMap::ResolveSpec(std::string_view spec,
                                    std::string_view base_dir) {
  std::string combined;
  if (!spec.empty() && spec.front() == '/') {
    combined.assign(spec);
  } else {
    combined.assign(base_dir);
    if (!combined.empty() && combined.back() != '/') combined += '/';
    combined.append(spec);
  }

  if (!combined.empty() && combined.back() == '/') combined += '*';

  bool absolute = false;
  auto segs = SplitSegments(combined, absolute);
  segs = Normalize(std::move(segs));
  return Join(segs, absolute);
}

bool LibraryMap::PathMatches(std::string_view spec, std::string_view base_dir,
                             std::string_view path) {
  if (spec.empty() || path.empty()) return false;
  std::string resolved_pat = ResolveSpec(spec, base_dir);

  bool pat_abs = false, path_abs = false;
  auto pat_segs = SplitSegments(resolved_pat, pat_abs);
  auto path_segs = SplitSegments(path, path_abs);
  path_segs = Normalize(std::move(path_segs));
  if (pat_abs != path_abs) return false;
  return GlobMatchSegments(pat_segs, 0, path_segs, 0);
}

void LibraryMap::AddDeclaration(const LibraryDecl& decl,
                                std::string_view base_dir) {
  for (auto path : decl.file_paths) {
    entries_.push_back(
        {std::string(decl.name), std::string(base_dir), std::string(path)});
  }
}

std::string_view LibraryMap::LibraryForFile(std::string_view path) const {
  bool found_any = false;
  SpecKind best = SpecKind::kDirectory;
  std::string_view chosen;
  bool ambiguous = false;

  for (const auto& e : entries_) {
    if (!PathMatches(e.spec, e.base_dir, path)) continue;
    SpecKind kind = ClassifySpec(e.spec);
    if (!found_any || static_cast<int>(kind) < static_cast<int>(best)) {
      found_any = true;
      best = kind;
      chosen = e.library;
      ambiguous = false;
    } else if (kind == best && e.library != chosen) {
      ambiguous = true;
    }
  }

  if (!found_any) return "work";
  if (ambiguous) return std::string_view{};
  return chosen;
}

void LibraryMap::WriteCell(std::string_view library, std::string_view name,
                           bool is_module, SourceLoc loc, DiagEngine& diag) {
  std::string key = CellKey(library, name);
  auto it = cells_.find(key);
  if (it != cells_.end()) {
    // Two modules of the same name written to one library in a single
    // invocation are almost certainly a mistake rather than a recompile.
    if (is_module && it->second.is_module &&
        it->second.from_current_invocation) {
      diag.Warning(loc, "module '" + std::string(name) +
                            "' is written to library '" + std::string(library) +
                            "' more than once in this invocation");
    }
    // The last cell encountered wins.
    it->second = LibraryCell{std::string(library), std::string(name), is_module,
                             loc, true};
    return;
  }
  cells_.emplace(std::move(key),
                 LibraryCell{std::string(library), std::string(name), is_module,
                             loc, true});
}

const LibraryCell* LibraryMap::CellInLibrary(std::string_view library,
                                             std::string_view name) const {
  auto it = cells_.find(CellKey(library, name));
  return it == cells_.end() ? nullptr : &it->second;
}

void LibraryMap::BeginNewInvocation() {
  for (auto& [key, cell] : cells_) cell.from_current_invocation = false;
}

std::vector<std::string_view> LibraryMap::LibraryDeclarationOrder() const {
  std::vector<std::string_view> order;
  std::unordered_set<std::string_view> seen;
  for (const auto& e : entries_) {
    if (seen.insert(e.library).second) {
      order.emplace_back(e.library);
    }
  }
  return order;
}

std::vector<std::string> LibraryMap::ResolveSearchOrder(
    const std::vector<std::string>& cli_override) const {
  if (!cli_override.empty()) return cli_override;
  std::vector<std::string> order;
  for (auto name : LibraryDeclarationOrder()) order.emplace_back(name);
  return order;
}

void LibraryMap::TagCompilationUnit(CompilationUnit& cu,
                                    std::string_view source_path) const {
  std::string_view lib = LibraryForFile(source_path);
  for (auto* m : cu.modules) m->library = lib;
  for (auto* i : cu.interfaces) i->library = lib;
  for (auto* p : cu.programs) p->library = lib;
  for (auto* c : cu.checkers) c->library = lib;
  for (auto* u : cu.udps) u->library = lib;
  for (auto* p : cu.packages) p->library = lib;
  for (auto* c : cu.configs) c->library = lib;
}

bool LibraryMap::LoadMapFile(const std::filesystem::path& map_file,
                             std::vector<std::string>* errors) {
  std::vector<std::filesystem::path> stack;
  return LoadMapFileImpl(map_file, stack, errors);
}

bool LibraryMap::LoadMapFileImpl(const std::filesystem::path& map_file,
                                 std::vector<std::filesystem::path>& stack,
                                 std::vector<std::string>* errors) {
  namespace fs = std::filesystem;
  std::error_code ec;
  fs::path canon = fs::weakly_canonical(map_file, ec);
  if (ec) canon = map_file;

  if (StackContainsPath(stack, canon, errors)) return false;

  std::string content;
  if (!ReadFileContent(canon, content, errors)) return false;

  Arena arena;
  auto* cu = ParseLibraryMapContent(canon, std::move(content), arena, errors);
  if (cu == nullptr) return false;

  std::string base_dir = canon.parent_path().string();
  for (auto* lib_decl : cu->libraries) {
    AddDeclaration(*lib_decl, base_dir);
  }

  stack.push_back(canon);
  bool ok = true;
  for (auto* inc : cu->lib_includes) {
    if (inc->file_path.empty()) {
      ok = false;
      continue;
    }
    fs::path inc_path = ResolveIncludePath(inc->file_path, canon);
    if (!LoadMapFileImpl(inc_path, stack, errors)) ok = false;
  }
  stack.pop_back();

  return ok;
}

}  // namespace delta
