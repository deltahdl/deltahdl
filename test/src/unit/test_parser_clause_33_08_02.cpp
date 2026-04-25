#include <gtest/gtest.h>

#include <array>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "parser/library_map.h"

using namespace delta;

namespace {

// The four files §33.8.2 enumerates in its example fixture.  Every
// resolver outcome the subclause spells out is a subset of this list,
// so each test computes "which of these four match?" and compares to
// the LRM-listed set.
constexpr std::array<std::string_view, 4> kFiles = {
    "/proj/lib1/rtl/a.v",
    "/proj/lib2/gates/a.v",
    "/proj/lib1/rtl/b.v",
    "/proj/lib2/gates/b.v",
};

std::set<std::string> ResolveSpec(std::string_view spec,
                                  std::string_view base_dir) {
  std::set<std::string> matched;
  for (auto file : kFiles) {
    if (LibraryMap::PathMatches(spec, base_dir, file)) {
      matched.emplace(file);
    }
  }
  return matched;
}

std::set<std::string> Expected(std::initializer_list<std::string_view> files) {
  std::set<std::string> out;
  for (auto f : files) out.emplace(f);
  return out;
}

// §33.8.2 absolute spec #1: "/proj/lib*/*/a.v" anchored at /proj picks
// both a.v files because the single-segment wildcards bind to lib1/rtl
// and lib2/gates respectively, while the literal a.v rejects the b.v
// siblings.
TEST(LibraryMapFilePathSpecExamples, AbsoluteStarPerSegmentPicksBothALeaves) {
  EXPECT_EQ(ResolveSpec("/proj/lib*/*/a.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib2/gates/a.v"}));
}

// §33.8.2 absolute spec #2: a relative ".../a.v" with /proj as base
// resolves to /proj/.../a.v; the hierarchical wildcard spans the
// lib*/<sub> intermediate segments and the literal a.v leaf rejects the
// b.v files.
TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsPicksBothALeaves) {
  EXPECT_EQ(ResolveSpec(".../a.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib2/gates/a.v"}));
}

// §33.8.2 absolute spec #3: "/proj/.../b.v" mirrors the previous case
// for the b.v leaves, demonstrating that "..." continues to span any
// number of directories regardless of how the leaf is named.
TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsPicksBothBLeaves) {
  EXPECT_EQ(ResolveSpec("/proj/.../b.v", "/proj"),
            Expected({"/proj/lib1/rtl/b.v", "/proj/lib2/gates/b.v"}));
}

// §33.8.2 absolute spec #4: ".../rtl/*.v" forces the penultimate
// segment to be exactly "rtl", so the lib2/gates files drop out and
// only the two files under lib1/rtl survive.  This pins the resolver's
// behavior when "..." is followed by a literal directory name.
TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsWithLiteralDir) {
  EXPECT_EQ(ResolveSpec(".../rtl/*.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

// §33.8.2 relative spec #1: "../lib2/gates/*.v" anchored at /proj/lib1
// must walk up one directory, descend into lib2/gates, and match both
// .v files there.  Files under /proj/lib1 must not match because the
// ".." rewrites the prefix to /proj/lib2.
TEST(LibraryMapFilePathSpecExamples, RelativeDotDotCrossesToSibling) {
  EXPECT_EQ(ResolveSpec("../lib2/gates/*.v", "/proj/lib1"),
            Expected({"/proj/lib2/gates/a.v", "/proj/lib2/gates/b.v"}));
}

// §33.8.2 relative spec #2: "./rtl/?.v" anchored at /proj/lib1 picks up
// both files under /proj/lib1/rtl whose stems are exactly one
// character long.  The single-character wildcard must bind to "a" and
// "b" but not cross past the directory boundary.
TEST(LibraryMapFilePathSpecExamples, RelativeQuestionWildcardPicksSingleChars) {
  EXPECT_EQ(ResolveSpec("./rtl/?.v", "/proj/lib1"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

// §33.8.2 relative spec #3: "./rtl/" — a directory spec with a
// trailing slash — must include every file under /proj/lib1/rtl.
// This is the same as "./rtl/*" in §33.3.1; §33.8.2 fixes that
// equivalence at the example level.
TEST(LibraryMapFilePathSpecExamples, RelativeDirectorySpecIncludesAllFiles) {
  EXPECT_EQ(ResolveSpec("./rtl/", "/proj/lib1"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

}  // namespace
