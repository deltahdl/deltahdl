#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_preprocessor.h"
#include "lexer/keywords.h"

using namespace delta;

namespace {

std::vector<KeywordVersion> MarkedVersions(const std::string& out) {
  std::vector<KeywordVersion> versions;
  for (size_t pos = 0; pos + 1 < out.size(); ++pos) {
    if (out[pos] != kKeywordMarker) continue;
    if (pos != 0 && out[pos - 1] != '\n') continue;
    versions.push_back(
        static_cast<KeywordVersion>(static_cast<uint8_t>(out[pos + 1])));
    ++pos;
  }
  return versions;
}

size_t EndOfLastMarker(const std::string& out) {
  size_t last = 0;
  for (size_t pos = 0; pos + 1 < out.size(); ++pos) {
    if (out[pos] != kKeywordMarker) continue;
    if (pos != 0 && out[pos - 1] != '\n') continue;
    last = pos + 2;
    ++pos;
  }
  return last;
}

size_t Newlines(const std::string& text) {
  return static_cast<size_t>(std::count(text.begin(), text.end(), '\n'));
}

constexpr const char* kM2Module =
    "module m2 (input wire clk, output wire q);\n"
    "  reg [63:0] logic;\n"
    "endmodule\n";

constexpr const char* kInterface =
    "interface if1 (input wire clk);\n"
    "  wire [7:0] data;\n"
    "endinterface\n";

std::string Guarded(const std::string& specifier, const std::string& body) {
  return "`begin_keywords \"" + specifier + "\"\n" + body + "`end_keywords\n";
}

TEST(KeywordVersionExamplePreproc, ModuleWithNoDirectiveIsLeftUnmarked) {
  PreprocFixture f;
  auto out = Preprocess("module m1;\n  reg [63:0] v;\nendmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(MarkedVersions(out).empty());
  EXPECT_NE(out.find("module m1;"), std::string::npos);
}

TEST(KeywordVersionExamplePreproc, ModuleAfterAClosedPairIsBackToTheDefault) {
  PreprocFixture f;
  auto out = Preprocess(Guarded("1364-2001", kM2Module) +
                            "module m1;\n  reg [63:0] v;\nendmodule\n",
                        f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 2u);
  EXPECT_EQ(versions[0], KeywordVersion::kVer13642001);
  EXPECT_EQ(versions[1], KeywordVersion::kVer18002023);

  auto module_pos = out.find("module m1;");
  ASSERT_NE(module_pos, std::string::npos);
  EXPECT_LT(EndOfLastMarker(out), module_pos);
}

TEST(KeywordVersionExamplePreproc, ModuleAheadOfTheFirstPairIsUnmarked) {
  PreprocFixture f;
  auto out = Preprocess("module m1;\n  reg [63:0] v;\nendmodule\n" +
                            Guarded("1364-2001", kM2Module),
                        f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 2u);
  EXPECT_EQ(versions[0], KeywordVersion::kVer13642001);

  auto module_pos = out.find("module m1;");
  ASSERT_NE(module_pos, std::string::npos);
  EXPECT_LT(module_pos, out.find(kKeywordMarker));
}

TEST(KeywordVersionExamplePreproc, EachModuleExampleSpecifierReachesTheMarker) {
  const std::pair<const char*, KeywordVersion> kCases[] = {
      {"1364-2001", KeywordVersion::kVer13642001},
      {"1364-1995", KeywordVersion::kVer13641995},
      {"1364-2005", KeywordVersion::kVer13642005},
      {"1800-2005", KeywordVersion::kVer18002005},
  };
  for (const auto& [specifier, expected] : kCases) {
    PreprocFixture f;
    auto out = Preprocess(Guarded(specifier, kM2Module), f);
    EXPECT_FALSE(f.diag.HasErrors()) << specifier;

    auto versions = MarkedVersions(out);
    ASSERT_EQ(versions.size(), 2u) << specifier;
    EXPECT_EQ(versions[0], expected) << specifier;

    EXPECT_NE(out.find("reg [63:0] logic;"), std::string::npos) << specifier;
    EXPECT_EQ(out.find("begin_keywords"), std::string::npos) << specifier;
  }
}

TEST(KeywordVersionExamplePreproc,
     EachInterfaceExampleSpecifierReachesTheMarker) {
  const std::pair<const char*, KeywordVersion> kCases[] = {
      {"1800-2005", KeywordVersion::kVer18002005},
      {"1364-2005", KeywordVersion::kVer13642005},
  };
  for (const auto& [specifier, expected] : kCases) {
    PreprocFixture f;
    auto out = Preprocess(Guarded(specifier, kInterface), f);
    EXPECT_FALSE(f.diag.HasErrors()) << specifier;

    auto versions = MarkedVersions(out);
    ASSERT_EQ(versions.size(), 2u) << specifier;
    EXPECT_EQ(versions[0], expected) << specifier;

    EXPECT_NE(out.find("interface if1"), std::string::npos) << specifier;
    EXPECT_NE(out.find("endinterface"), std::string::npos) << specifier;
  }
}

TEST(KeywordVersionExamplePreproc, BeginKeywordsLineIsOneLineOfOutput) {
  const std::string kSrc =
      "`begin_keywords \"1364-2001\"\n"
      "module m2;\n"
      "  reg [63:0] v;\n"
      "endmodule\n";
  PreprocFixture f;
  auto out = Preprocess(kSrc, f);

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 1u);
  EXPECT_EQ(versions[0], KeywordVersion::kVer13642001);

  EXPECT_EQ(Newlines(out), Newlines(kSrc));
}

TEST(KeywordVersionExamplePreproc, EndKeywordsLineIsOneLineOfOutput) {
  const std::string kSrc =
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n"
      "module m1;\n"
      "  reg [63:0] v;\n"
      "endmodule\n";
  PreprocFixture f;
  auto out = Preprocess(kSrc, f);
  EXPECT_FALSE(f.diag.HasErrors());

  auto versions = MarkedVersions(out);
  ASSERT_EQ(versions.size(), 2u);
  EXPECT_EQ(versions[1], KeywordVersion::kVer18002023);

  EXPECT_EQ(Newlines(out), Newlines(kSrc));
}

}  // namespace
