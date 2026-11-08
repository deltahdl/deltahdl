#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <set>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"

namespace delta {
namespace {

class ExtendedVcdKeywordCommands : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src, bool close_file = false,
                     std::string_view driver_comment = {}) {
    return RunVcdDump(src, {.scope = "t",
                            .driver_comment = driver_comment,
                            .close_file = close_file});
  }
};

bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}

std::set<std::string> KeywordCommands(const std::vector<std::string>& toks) {
  std::set<std::string> kws;
  for (const auto& t : toks) {
    if (t[0] == '$' && t != "$end") kws.insert(t);
  }
  return kws;
}

const std::set<std::string>& FourStateKeywords() {
  static const std::set<std::string> kKeywords = {
      "$comment",  "$date",           "$dumpall", "$dumpoff",   "$dumpon",
      "$dumpvars", "$enddefinitions", "$scope",   "$timescale", "$upscope",
      "$var",      "$version"};
  return kKeywords;
}

struct SectionScan {
  std::vector<std::string> body;
  bool closed = false;
};
SectionScan ScanSection(const std::vector<std::string>& toks,
                        std::string_view keyword) {
  SectionScan scan;
  size_t i = 0;
  while (i < toks.size() && toks[i] != keyword) ++i;
  for (++i; i < toks.size(); ++i) {
    if (toks[i][0] == '$') {
      scan.closed = (toks[i] == "$end");
      return scan;
    }
    scan.body.push_back(toks[i]);
  }
  return scan;
}

std::set<std::string> ExtraKeywords(const std::string& content) {
  std::set<std::string> extra;
  for (const auto& kw : KeywordCommands(Tokens(content))) {
    if (FourStateKeywords().count(kw) == 0) extra.insert(kw);
  }
  return extra;
}

const char* const kExtendedSrc =
    "module t;\n"
    "  logic a;\n"
    "  initial begin\n"
    "    a = 1'b0;\n"
    "    $dumpports(, \"dump2.dump\");\n"
    "    #10 a = 1'b1;\n"
    "  end\n"
    "endmodule\n";

TEST_F(ExtendedVcdKeywordCommands, GeneralInfoSectionsAreKeywordBounded) {
  auto content = RunVcd(kExtendedSrc);
  auto toks = Tokens(content);
  struct Section {
    const char* keyword;
    const char* info;
  } sections[] = {
      {"$date", nullptr}, {"$version", "DeltaHDL"}, {"$timescale", "1ns"}};
  for (const auto& s : sections) {
    auto scan = ScanSection(toks, s.keyword);
    EXPECT_TRUE(scan.closed) << s.keyword << " section not closed by $end";
    ASSERT_FALSE(scan.body.empty()) << s.keyword << " section is empty";
    if (s.info != nullptr) {
      EXPECT_NE(std::find(scan.body.begin(), scan.body.end(), s.info),
                scan.body.end())
          << s.info << " escapes its section";
    }
  }
}

TEST_F(ExtendedVcdKeywordCommands,
       ProductionDumperInsertsInfoAsKeywordSection) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    $dumpportslimit(300);\n"
      "    repeat (40) #1 a = ~a;\n"
      "  end\n"
      "endmodule\n");
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  auto p_comment = content.find("$comment", p_defs_end);
  ASSERT_NE(p_comment, std::string::npos) << "no dumper-inserted section";
  auto toks = Tokens(content);
  auto scan = ScanSection(toks, "$comment");
  EXPECT_TRUE(scan.closed);
  bool notice_inside = false;
  for (const auto& w : scan.body) {
    if (w.find("reached") != std::string::npos) notice_inside = true;
  }
  EXPECT_TRUE(notice_inside);
  EXPECT_TRUE(NoFusedCommands(toks));
}

TEST_F(ExtendedVcdKeywordCommands, DriverSuppliedInfoIsKeywordBounded) {
  auto content = RunVcd(kExtendedSrc, false, "chip revision B2 baseline");
  auto toks = Tokens(content);
  auto scan = ScanSection(toks, "$comment");
  EXPECT_TRUE(scan.closed);
  EXPECT_EQ(scan.body,
            (std::vector<std::string>{"chip", "revision", "B2", "baseline"}));
  EXPECT_TRUE(NoFusedCommands(toks));
}

TEST_F(ExtendedVcdKeywordCommands, OpenExtendedFileUsesOnlyInheritedKeywords) {
  auto content = RunVcd(kExtendedSrc, false);
  ASSERT_NE(content.find("$enddefinitions"), std::string::npos);
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_TRUE(ExtraKeywords(content).empty());
}

TEST_F(ExtendedVcdKeywordCommands, FourStateFileGainsNoAdditionalKeyword) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      true);
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_TRUE(ExtraKeywords(content).empty());
}

TEST_F(ExtendedVcdKeywordCommands, TaskReachedFromAlwaysStillOneAddition) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic go;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    go = 1'b0;\n"
      "    #5 go = 1'b1;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "  always @(posedge go) $dumpports(, \"dump2.dump\");\n"
      "endmodule\n",
      true);
  ASSERT_NE(content.find("#15"), std::string::npos);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
  auto toks = Tokens(content);
  EXPECT_TRUE(NoFusedCommands(toks));
}

TEST_F(ExtendedVcdKeywordCommands, InheritedControlSectionsAreNotAdditions) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 $dumpportsall;\n"
      "    #10 $dumpportsoff;\n"
      "    #10 $dumpportson;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      true);
  auto toks = Tokens(content);
  EXPECT_GE(CountToken(toks, "$dumpall"), 1u);
  EXPECT_GE(CountToken(toks, "$dumpoff"), 1u);
  EXPECT_GE(CountToken(toks, "$dumpon"), 1u);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  size_t openers = 0;
  size_t ends = 0;
  for (const auto& t : toks) {
    if (t[0] != '$') continue;
    (t == "$end" ? ends : openers)++;
  }
  EXPECT_EQ(openers, ends);
}

TEST_F(ExtendedVcdKeywordCommands, TaskBodyDumpportsStillOneAddition) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    start_dump;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      true);
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
}

TEST_F(ExtendedVcdKeywordCommands, SectionSeriesUnbrokenByAllValueForms) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  real r;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 8'b00000000;\n"
      "    r = 0.5;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 r = 2.75;\n"
      "    #10 s = 1'bx;\n"
      "    #10 s = 1'bz;\n"
      "  end\n"
      "endmodule\n",
      true);
  auto toks = Tokens(content);
  EXPECT_GE(CountToken(toks, "b10xz01zx"), 1u);
  EXPECT_GE(CountToken(toks, "r2.75"), 1u);
  EXPECT_GE(CountToken(toks, "x\""), 1u);
  EXPECT_GE(CountToken(toks, "z\""), 1u);
  EXPECT_TRUE(NoFusedCommands(toks));
  size_t openers = 0;
  size_t ends = 0;
  for (const auto& t : toks) {
    if (t[0] != '$') continue;
    (t == "$end" ? ends : openers)++;
  }
  EXPECT_EQ(openers, ends);
  EXPECT_EQ(ExtraKeywords(content).size(), 1u);
}

}  // namespace
}  // namespace delta
