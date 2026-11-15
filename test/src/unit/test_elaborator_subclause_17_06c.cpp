#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kReport =
    "the formal 'mode' of checker 'c', which a covergroup references, has a "
    "const actual";

std::vector<uint32_t> LinesHolding(std::string_view src,
                                   std::string_view what) {
  std::vector<uint32_t> lines;
  for (size_t at = src.find(what); at != std::string_view::npos;
       at = src.find(what, at + 1)) {
    lines.push_back(
        static_cast<uint32_t>(std::count(src.begin(), src.begin() + at, '\n')) +
        1);
  }
  return lines;
}

void ExpectConstActuals(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : LinesHolding(src, "u_bad")) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "17.6")) << line;
  }
  for (uint32_t line : LinesHolding(src, "u_ok")) {
    EXPECT_FALSE(ReportedError(diags, kReport, line, "17.6")) << line;
  }
}

std::string Checker(const std::string& items) {
  std::string src =
      "checker c(logic clk, logic [1:0] mode, logic [1:0] a, logic en);\n";
  src += items;
  src += "endchecker\n";
  return src;
}

const char* const kCovered =
    "  covergroup cg @(posedge clk);\n"
    "    cp: coverpoint mode;\n"
    "  endgroup\n"
    "  cg cg_1 = new();\n";

const char* const kVars =
    "  logic clk, en;\n"
    "  logic [1:0] x, y;\n";

const char* const kPair =
    "  c u_bad(clk, const'(x), y, en);\n"
    "  c u_ok(clk, x, y, en);\n";

std::string InTop(const std::string& items, const std::string& body) {
  std::string src = Checker(items);
  src += "module top;\n";
  src += kVars;
  src += body;
  src += "endmodule\n";
  return src;
}

TEST(CheckerCovergroupConstActual, EachFormOfConnectionIsChecked) {
  ExpectConstActuals(InTop(kCovered,
                           "  c u_bad1(.clk, .mode(const'(x)), .a(y), .en);\n"
                           "  c u_ok1(.clk, .mode(x), .a(y), .en);\n"
                           "  c u_bad2(clk, x | const'(y), y, en);\n"
                           "  c u_ok2(clk, x | y, y, en);\n"
                           "  wire [1:0] mode = x, a = y;\n"
                           "  c u_ok3(.clk, .mode, .a, .en);\n"
                           "  c u_ok4(.*);\n"));
}

TEST(CheckerCovergroupConstActual, AConstDefaultActualIsReported) {
  const std::string kSrc =
      "module top;\n"
      "  logic clk;\n"
      "  logic [1:0] x, y;\n"
      "  checker c(logic clk, logic [1:0] mode = const'(x));\n"
      "    covergroup cg @(posedge clk);\n"
      "      cp: coverpoint mode;\n"
      "    endgroup\n"
      "    cg cg_1 = new();\n"
      "  endchecker\n"
      "  checker d(logic clk, logic [1:0] mode = y);\n"
      "    covergroup cg @(posedge clk);\n"
      "      cp: coverpoint mode;\n"
      "    endgroup\n"
      "    cg cg_1 = new();\n"
      "  endchecker\n"
      "  c u_bad(clk);\n"
      "  d u_ok(clk);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport,
                            LineHolding(kSrc, "const'(x)"), "17.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

std::string InEachOtherScope(const std::string& body) {
  std::string src = Checker(kCovered);
  src += "interface ifc;\n";
  src += kVars;
  src += body;
  src += "endinterface\nprogram prg;\n";
  src += kVars;
  src += body;
  src +=
      "endprogram\n"
      "checker w(logic clk, en, logic [1:0] x, y);\n";
  src += body;
  src += "endchecker\nmodule top;\n";
  src += kVars;
  src +=
      "  ifc i();\n"
      "  prg p();\n"
      "  w wi(clk, en, x, y);\n"
      "endmodule\n";
  return src;
}

TEST(CheckerCovergroupConstActual, EachTopLevelOfAnInstantiatingScope) {
  ExpectConstActuals(InEachOtherScope(kPair));
}

TEST(CheckerCovergroupConstActual,
     DISABLED_EachGenerateBlockOfAModuleIsChecked) {
  ExpectConstActuals(InTop(kCovered,
                           "  if (1) begin : g\n"
                           "    c u_bad1(clk, const'(x), y, en);\n"
                           "    c u_ok1(clk, x, y, en);\n"
                           "  end\n"
                           "  for (genvar i = 0; i < 1; i++) begin : h\n"
                           "    c u_bad2(clk, const'(x), y, en);\n"
                           "  end\n"
                           "  case (1)\n"
                           "    1: begin : k\n"
                           "      c u_bad3(clk, const'(x), y, en);\n"
                           "    end\n"
                           "  endcase\n"));
}

TEST(CheckerCovergroupConstActual,
     DISABLED_AGenerateBlockOfEachOtherScopeIsChecked) {
  ExpectConstActuals(
      InEachOtherScope("  if (1) begin : g\n"
                       "    c u_bad(clk, const'(x), y, en);\n"
                       "    c u_ok(clk, x, y, en);\n"
                       "  end\n"));
}

TEST(CheckerCovergroupConstActual, AProceduralInstanceIsChecked) {
  ExpectConstActuals(InTop(kCovered,
                           "  always @(posedge clk) begin\n"
                           "    c u_bad1(clk, const'(x), y, en);\n"
                           "    c u_ok1(clk, x, y, en);\n"
                           "  end\n"
                           "  initial begin\n"
                           "    c u_bad2(clk, const'(x), y, en);\n"
                           "  end\n"
                           "  if (1) begin : g\n"
                           "    always @(posedge clk) begin\n"
                           "      c u_bad3(clk, const'(x), y, en);\n"
                           "    end\n"
                           "  end\n"));
}

struct Reference {
  const char* where;
  const char* items;
};

void ExpectEachReference(const std::vector<Reference>& references) {
  for (const auto& reference : references) {
    SCOPED_TRACE(reference.where);
    ExpectConstActuals(InTop(reference.items, kPair));
  }
}

TEST(CheckerCovergroupConstActual,
     AnEventCoverpointOrGuardNamingTheFormalIsReported) {
  ExpectEachReference({
      {"clocking event",
       "  covergroup cg @(posedge mode[0]);\n"
       "    cp: coverpoint a;\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"coverpoint operand",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint a + mode;\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"coverpoint iff",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint a iff (mode[0]);\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"never instantiated",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint mode;\n"
       "  endgroup\n"},
  });
}

TEST(CheckerCovergroupConstActual,
     DISABLED_ABinOptionCrossOrArgumentNamingTheFormalIsReported) {
  ExpectEachReference({
      {"cross iff",
       "  covergroup cg @(posedge clk);\n"
       "    cpa: coverpoint a;\n"
       "    cpb: coverpoint en;\n"
       "    xab: cross cpa, cpb iff (mode[0]);\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"bin value list",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint a { bins b = {mode}; }\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"bin with clause",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint a { bins b[] = {[0:3]} with (item <= mode); }\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"cross bin select",
       "  covergroup cg @(posedge clk);\n"
       "    cpa: coverpoint a;\n"
       "    cpb: coverpoint en;\n"
       "    xab: cross cpa, cpb { bins s = binsof(cpa) intersect {mode}; }\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"covergroup option",
       "  covergroup cg @(posedge clk);\n"
       "    option.weight = mode;\n"
       "    cp: coverpoint a;\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"coverpoint option",
       "  covergroup cg @(posedge clk);\n"
       "    cp: coverpoint a { option.weight = mode; }\n"
       "  endgroup\n"
       "  cg cg_1 = new();\n"},
      {"constructor argument",
       "  covergroup cg (int w) @(posedge clk);\n"
       "    cp: coverpoint a;\n"
       "  endgroup\n"
       "  cg cg_1 = new(mode);\n"},
  });
}

TEST(CheckerCovergroupConstActual,
     DISABLED_ACovergroupInAGenerateBlockNamingTheFormalIsReported) {
  ExpectEachReference({
      {"if generate block",
       "  if (1) begin : g\n"
       "    covergroup cg @(posedge clk);\n"
       "      cp: coverpoint mode;\n"
       "    endgroup\n"
       "    cg cg_1 = new();\n"
       "  end\n"},
      {"for generate block",
       "  for (genvar i = 0; i < 1; i++) begin : g\n"
       "    covergroup cg @(posedge clk);\n"
       "      cp: coverpoint mode;\n"
       "    endgroup\n"
       "    cg cg_1 = new();\n"
       "  end\n"},
      {"case generate block",
       "  case (1)\n"
       "    1: begin : g\n"
       "      covergroup cg @(posedge clk);\n"
       "        cp: coverpoint mode;\n"
       "      endgroup\n"
       "      cg cg_1 = new();\n"
       "    end\n"
       "  endcase\n"},
  });
}

TEST(CheckerCovergroupConstActual, AFormalOnlyAnAssertionNamesIsAccepted) {
  ExpectConstActuals(
      InTop("  a1: assert property (@(posedge clk) mode != 2'b11);\n",
            "  c u_ok(clk, const'(x), y, en);\n"));
}

TEST(CheckerCovergroupConstActual,
     DISABLED_AFormalACovergroupArgumentShadowsIsAccepted) {
  ExpectConstActuals(
      InTop("  covergroup cg (int mode) @(posedge clk);\n"
            "    cp: coverpoint mode;\n"
            "  endgroup\n"
            "  cg cg_1 = new(1);\n",
            "  c u_ok(clk, const'(x), y, en);\n"));
}

TEST(CheckerCovergroupConstActual, ACustomSampleArgumentIsReportedOnce) {
  const std::string kSrc = InTop(
      "  covergroup cg with function sample(bit [1:0] v);\n"
      "    cp: coverpoint v;\n"
      "  endgroup\n"
      "  cg cg_1 = new();\n"
      "  always_ff @(posedge clk) cg_1.sample(mode);\n",
      "  c u_ok(clk, const'(x), y, en);\n");
  ExpectConstActuals(kSrc);
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is used in a continuous assignment or procedural "
                            "code",
                            LineHolding(kSrc, "u_ok"), "17.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
