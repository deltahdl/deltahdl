#include "parser/library_map.h"

#include "parser/ast.h"

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
  for (const auto& e : entries_) {
    if (PathMatches(e.spec, e.base_dir, path)) return e.library;
  }
  // §33.3.1: any file unmatched by a declared library belongs to "work".
  return "work";
}

}  // namespace delta
