#include "parser/library_map.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/ast_specify.h"
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
  std::filesystem::path inc_path{std::string{UnquoteSpec(file_path)}};
  if (inc_path.is_relative()) {
    inc_path = canon.parent_path() / inc_path;
  }
  return inc_path;
}

bool IsWildSegment(std::string_view seg) {
  return seg.find_first_of("*?") != std::string_view::npos ||
         seg.find("...") != std::string_view::npos;
}

std::string ResolveFixedDirectories(const std::string& resolved) {
  bool absolute = false;
  auto segs = SplitSegments(resolved, absolute);
  if (!absolute) return resolved;
  std::size_t fixed = 0;
  while (fixed + 1 < segs.size() && !IsWildSegment(segs[fixed])) ++fixed;
  if (fixed == 0) return resolved;
  std::vector<std::string_view> head(
      segs.begin(), segs.begin() + static_cast<std::ptrdiff_t>(fixed));
  std::error_code ec;
  const std::filesystem::path kCanon =
      std::filesystem::weakly_canonical(Join(head, true), ec);
  if (ec) return resolved;
  std::string out = kCanon.string();
  for (std::size_t i = fixed; i < segs.size(); ++i) {
    out += '/';
    out.append(segs[i]);
  }
  return out;
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
  std::string resolved_pat =
      ResolveFixedDirectories(ResolveSpec(spec, base_dir));

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
  SourceLoc loc = mgr_ == nullptr ? SourceLoc::None() : decl.range.start;
  for (auto path : decl.file_paths) {
    entries_.push_back({std::string(decl.name), std::string(base_dir),
                        std::string(path), loc});
  }
}

static std::string ComparedSourcePath(std::string_view path) {
  namespace fs = std::filesystem;
  fs::path written{std::string(path)};
  if (!written.is_absolute()) return std::string(path);
  std::error_code ec;
  fs::path canon = fs::weakly_canonical(written, ec);
  return ec ? std::string(path) : canon.string();
}

std::vector<const LibraryMap::Entry*> LibraryMap::EntriesClaiming(
    std::string_view path) const {
  SpecKind best = SpecKind::kDirectory;
  std::vector<const Entry*> claimants;
  const std::string kCompared = ComparedSourcePath(path);

  for (const auto& e : entries_) {
    if (!PathMatches(e.spec, e.base_dir, kCompared)) continue;
    SpecKind kind = ClassifySpec(e.spec);
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
    if (is_module && it->second.is_module &&
        it->second.from_current_invocation) {
      diag.Warning(loc,
                   "module '" + std::string(name) +
                       "' is written to library '" + std::string(library) +
                       "' more than once in this invocation",
                   Subclause("33.3.1.1"));
    }
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
    if (seen.insert(name).second) order.push_back(name);
  }

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

  auto arena = std::make_shared<Arena>();
  if (mgr_ == nullptr && own_mgr_ == nullptr) {
    own_mgr_ = std::make_shared<SourceManager>();
  }
  SourceManager* parse_mgr = mgr_ != nullptr ? mgr_ : own_mgr_.get();
  auto* cu = ParseLibraryMapContent(canon, std::move(content), *arena,
                                    parse_mgr, errors);
  if (cu == nullptr) return false;
  arenas_.push_back(arena);
  for (auto* cfg : cu->configs) map_configs_.emplace_back(cfg, canon.string());

  stack.push_back(canon);
  const bool kOk = LoadDescriptionsInOrder(*cu, canon, stack, errors);
  stack.pop_back();
  return kOk;
}

bool LibraryMap::LoadDescriptionsInOrder(
    const CompilationUnit& cu, const std::filesystem::path& canon,
    std::vector<std::filesystem::path>& stack,
    std::vector<std::string>* errors) {
  const auto kBefore = [](SourceLoc a, SourceLoc b) {
    return std::tie(a.line, a.column) < std::tie(b.line, b.column);
  };
  const std::string kBaseDir = canon.parent_path().string();
  std::size_t lib = 0;
  bool ok = true;
  for (const IncludeStmt* inc : cu.lib_includes) {
    while (lib < cu.libraries.size() &&
           kBefore(cu.libraries[lib]->range.start, inc->loc)) {
      AddDeclaration(*cu.libraries[lib++], kBaseDir);
    }
    if (!LoadMapFileImpl(ResolveIncludePath(inc->file_path, canon), stack,
                         errors)) {
      ok = false;
    }
  }
  while (lib < cu.libraries.size()) {
    AddDeclaration(*cu.libraries[lib++], kBaseDir);
  }
  return ok;
}

std::vector<ConfigDecl*> LibraryMap::DeclaredConfigs() const {
  std::vector<ConfigDecl*> configs;
  configs.reserve(map_configs_.size());
  for (const auto& [cfg, map_file] : map_configs_) {
    cfg->library = LibraryForFile(map_file);
    configs.push_back(cfg);
  }
  return configs;
}

}  // namespace delta
