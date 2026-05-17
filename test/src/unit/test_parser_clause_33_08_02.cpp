#include <gtest/gtest.h>

#include <array>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "parser/library_map.h"

using namespace delta;

namespace {

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

TEST(LibraryMapFilePathSpecExamples, AbsoluteStarPerSegmentPicksBothALeaves) {
  EXPECT_EQ(ResolveSpec("/proj/lib*/*/a.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib2/gates/a.v"}));
}

TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsPicksBothALeaves) {
  EXPECT_EQ(ResolveSpec(".../a.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib2/gates/a.v"}));
}

TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsPicksBothBLeaves) {
  EXPECT_EQ(ResolveSpec("/proj/.../b.v", "/proj"),
            Expected({"/proj/lib1/rtl/b.v", "/proj/lib2/gates/b.v"}));
}

TEST(LibraryMapFilePathSpecExamples, AbsoluteHierarchicalDotsWithLiteralDir) {
  EXPECT_EQ(ResolveSpec(".../rtl/*.v", "/proj"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

TEST(LibraryMapFilePathSpecExamples, RelativeDotDotCrossesToSibling) {
  EXPECT_EQ(ResolveSpec("../lib2/gates/*.v", "/proj/lib1"),
            Expected({"/proj/lib2/gates/a.v", "/proj/lib2/gates/b.v"}));
}

TEST(LibraryMapFilePathSpecExamples, RelativeQuestionWildcardPicksSingleChars) {
  EXPECT_EQ(ResolveSpec("./rtl/?.v", "/proj/lib1"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

TEST(LibraryMapFilePathSpecExamples, RelativeDirectorySpecIncludesAllFiles) {
  EXPECT_EQ(ResolveSpec("./rtl/", "/proj/lib1"),
            Expected({"/proj/lib1/rtl/a.v", "/proj/lib1/rtl/b.v"}));
}

}
