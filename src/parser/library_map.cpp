#include "parser/library_map.h"

#include <algorithm>
#include <cstdint>
#include <filesystem>
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

// A file path specification is written in whatever notation names a path on
// the host filesystem, and a path written between double quotes is one such
// notation: there the quotes delimit the path rather than belong to it, and a
// name carrying a space is why the notation exists. Peeling a surrounding pair
// off before the specification is read makes the quoted and the bare spelling
// of one path name that same path.
//
// A quote that is not matched by one at the other end is left where it is,
// since a file name is free to carry a quote of its own; only the surrounding
// pair is notation.
std::string_view UnquoteSpec(std::string_view spec) {
  if (spec.size() < 2 || spec.front() != '"' || spec.back() != '"') {
    return spec;
  }
  return spec.substr(1, spec.size() - 2);
}

enum class SpecKind : std::uint8_t {
  kExplicitFilename = 0,
  kWildcardFilename = 1,
  kDirectory = 2,
};

SpecKind ClassifySpec(std::string_view raw_spec) {
  std::string_view spec = UnquoteSpec(raw_spec);
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

// The characters an identifier is built from: a letter or an underscore opens
// one, and digits and dollar signs may follow.
bool IsNameStart(char c) {
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_';
}

bool IsNameBody(char c) {
  return IsNameStart(c) || (c >= '0' && c <= '9') || c == '$';
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

// Parses one map file, registering it in `external` when a caller supplied one
// and in a manager private to this parse when it did not. A position taken off
// the parse means something only to the manager the file was registered in, so
// a caller that reports a library declaration passes the manager its reports
// resolve against and gets positions it can use.
CompilationUnit* ParseLibraryMapContent(const std::filesystem::path& canon,
                                        std::string content, Arena& arena,
                                        SourceManager* external,
                                        std::vector<std::string>* errors) {
  SourceManager own;
  SourceManager& mgr = external == nullptr ? own : *external;
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

std::string LibraryMap::ResolveSpec(std::string_view raw_spec,
                                    std::string_view base_dir) {
  std::string_view spec = UnquoteSpec(raw_spec);
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
  segs = Normalize(segs);
  return Join(segs, absolute);
}

bool LibraryMap::PathMatches(std::string_view spec, std::string_view base_dir,
                             std::string_view path) {
  if (UnquoteSpec(spec).empty() || path.empty()) return false;
  std::string resolved_pat = ResolveSpec(spec, base_dir);

  bool pat_abs = false, path_abs = false;
  auto pat_segs = SplitSegments(resolved_pat, pat_abs);
  auto path_segs = SplitSegments(path, path_abs);
  path_segs = Normalize(path_segs);
  if (pat_abs != path_abs) return false;
  return GlobMatchSegments(pat_segs, 0, path_segs, 0);
}

void LibraryMap::ResolvePositionsAgainst(SourceManager& mgr) { mgr_ = &mgr; }

void LibraryMap::AddDeclaration(const LibraryDecl& decl,
                                std::string_view base_dir) {
  // The position of a declaration is kept only where this map parses into the
  // manager its caller reports through. A file identifier issued by any other
  // manager names a different file there, so a report standing at such a
  // position would name the wrong file and the wrong line, which is worse than
  // standing at no position at all.
  SourceLoc loc = mgr_ == nullptr ? SourceLoc::None() : decl.range.start;
  for (auto path : decl.file_paths) {
    entries_.push_back({std::string(decl.name), std::string(base_dir),
                        std::string(path), loc});
  }
}

std::vector<const LibraryMap::Entry*> LibraryMap::EntriesClaiming(
    std::string_view path) const {
  SpecKind best = SpecKind::kDirectory;
  std::vector<const Entry*> claimants;

  for (const auto& e : entries_) {
    if (!PathMatches(e.spec, e.base_dir, path)) continue;
    SpecKind kind = ClassifySpec(e.spec);
    // A more specific specification settles the claim on its own, so the
    // specifications claiming the file less specifically drop out.
    if (claimants.empty() || static_cast<int>(kind) < static_cast<int>(best)) {
      best = kind;
      claimants.clear();
      claimants.push_back(&e);
    } else if (kind == best) {
      claimants.push_back(&e);
    }
  }
  return claimants;
}

std::vector<std::string_view> LibraryMap::LibrariesForFile(
    std::string_view path) const {
  std::vector<std::string_view> libraries;
  // One library claiming a file through two of its own specifications is named
  // once: the ambiguity this answers is between libraries, and a library is
  // not ambiguous with itself.
  for (const Entry* e : EntriesClaiming(path)) {
    if (std::find(libraries.begin(), libraries.end(), e->library) ==
        libraries.end()) {
      libraries.emplace_back(e->library);
    }
  }
  return libraries;
}

SourceLoc LibraryMap::FirstDeclarationClaiming(std::string_view path) const {
  auto claimants = EntriesClaiming(path);
  if (claimants.empty()) return SourceLoc::None();
  return claimants.front()->loc;
}

std::string_view LibraryMap::LibraryForFile(std::string_view path) const {
  auto claimants = LibrariesForFile(path);
  if (claimants.empty()) return "work";
  if (claimants.size() > 1) return std::string_view{};
  return claimants.front();
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
      diag.Warning(loc,
                   "module '" + std::string(name) +
                       "' is written to library '" + std::string(library) +
                       "' more than once in this invocation",
                   Subclause("33.3.1.1"));
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

bool LibraryMap::IsLibraryName(std::string_view name) {
  if (name.empty() || !IsNameStart(name.front())) return false;
  for (char c : name.substr(1)) {
    if (!IsNameBody(c)) return false;
  }
  return true;
}

std::vector<std::string> LibraryMap::ResolveSearchOrder(
    const std::vector<std::string>& cli_override,
    std::vector<std::string>* errors) const {
  std::vector<std::string> order;
  std::unordered_set<std::string_view> seen;
  for (const auto& name : cli_override) {
    if (!IsLibraryName(name)) {
      if (errors != nullptr) {
        errors->push_back("library search order entry '" + name +
                          "' is not a library name");
      }
      continue;
    }
    // A name given twice ranks its library once: the earlier position is the
    // one a search reaches, so the later mention says nothing further.
    if (seen.insert(name).second) order.push_back(name);
  }

  // An override says where the libraries it names belong; it says nothing
  // about how the rest rank among themselves, and what this map declares is
  // the default answer to exactly that. So every library the override passed
  // over follows the ones it named, keeping the position its declaration gave
  // it. Leaving them out instead would leave them tied, and a tie between two
  // libraries holding a cell of one name is settled by whichever description
  // was read first -- which is to say by the order the sources were handed
  // over, an order no library map and no command line ever stated.
  for (auto name : LibraryDeclarationOrder()) {
    if (seen.insert(name).second) order.emplace_back(name);
  }
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
  auto* cu =
      ParseLibraryMapContent(canon, std::move(content), arena, mgr_, errors);
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
