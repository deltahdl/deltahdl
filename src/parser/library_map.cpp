#include "parser/library_map.h"

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

// Split `path` on '/' into segments; keep the absolute marker in `absolute`.
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

// Apply `.` (skip) and `..` (pop previous concrete segment) per §33.3.1.
// `...` and wildcard tokens (`*`, `?`) are preserved verbatim.
std::vector<std::string_view> Normalize(std::vector<std::string_view> segs) {
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
  // Match a single path-component name against a pattern segment that may
  // contain `*` and `?`.  The component never crosses '/', so neither
  // wildcard advances past a '/'.
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

// §33.3.1.1 spec-type priority: smaller value wins.
enum class SpecKind : int {
  kExplicitFilename = 0,
  kWildcardFilename = 1,
  kDirectory = 2,
};

// Classify a file_path_spec by its trailing form.  The hierarchical
// wildcard `...` denotes directories, so a spec ending with `...` is
// also classified as a directory match.
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

bool GlobMatchSegments(const std::vector<std::string_view>& pat_segs,
                       size_t pi,
                       const std::vector<std::string_view>& path_segs,
                       size_t si) {
  if (pi == pat_segs.size()) return si == path_segs.size();
  if (pat_segs[pi] == "...") {
    // Hierarchical wildcard: zero or more whole segments.
    for (size_t k = si; k <= path_segs.size(); ++k) {
      if (GlobMatchSegments(pat_segs, pi + 1, path_segs, k)) return true;
    }
    return false;
  }
  if (si == path_segs.size()) return false;
  if (!GlobOne(pat_segs[pi], path_segs[si])) return false;
  return GlobMatchSegments(pat_segs, pi + 1, path_segs, si + 1);
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
  // Trailing '/' means "all files in that directory" — same as "/*".
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
    entries_.push_back({std::string(decl.name), std::string(base_dir),
                        std::string(path)});
  }
}

std::string_view LibraryMap::LibraryForFile(std::string_view path) const {
  // §33.3.1.1 file-path resolution: collect every entry that matches, keep
  // only the highest-priority spec-type tier, and surface cross-library
  // ambiguity within that tier as an empty return.  §33.3.1's "work"
  // fallback applies only when nothing matches at all.
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
  // §33.8.1: a non-empty CLI list overrides the lib.map's declaration
  // order outright — it does not merge or splice with the map.  The
  // override is names only, so any module's library label must already
  // have been assigned from the lib.map for the override to bind it.
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

  // §33.3.2 says the include behaves "as though the contents appear in
  // place"; with cycles that would never terminate, so detect and abort.
  for (const auto& p : stack) {
    if (p == canon) {
      if (errors) {
        errors->push_back("library map cycle including " + canon.string());
      }
      return false;
    }
  }

  std::ifstream ifs(canon);
  if (!ifs.good()) {
    if (errors) {
      errors->push_back("cannot open library map file " + canon.string());
    }
    return false;
  }
  std::ostringstream buf;
  buf << ifs.rdbuf();
  std::string content = buf.str();

  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  uint32_t fid = mgr.AddFile(canon.string(), std::move(content));
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  auto* cu = parser.ParseLibraryText();

  if (diag.HasErrors() || cu == nullptr) {
    if (errors) {
      errors->push_back("parse errors in library map file " + canon.string());
    }
    return false;
  }

  // §33.3.2: relative paths in library statements anchor to the
  // containing file's directory; AddDeclaration takes that directory as
  // base_dir, so the existing §33.3.1 evaluator handles the resolution.
  std::string base_dir = canon.parent_path().string();
  for (auto* lib_decl : cu->libraries) {
    AddDeclaration(*lib_decl, base_dir);
  }

  // §33.3.2: relative include paths anchor to the containing file's
  // directory; recurse with the resolved absolute path so subsequent
  // levels see their own parent dir as base.
  stack.push_back(canon);
  bool ok = true;
  for (auto* inc : cu->lib_includes) {
    if (inc->file_path.empty()) {
      ok = false;
      continue;
    }
    fs::path inc_path(std::string{inc->file_path});
    if (inc_path.is_relative()) {
      inc_path = canon.parent_path() / inc_path;
    }
    if (!LoadMapFileImpl(inc_path, stack, errors)) ok = false;
  }
  stack.pop_back();

  return ok;
}

}  // namespace delta
