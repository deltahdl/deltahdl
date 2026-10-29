

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, TriregChargeStrengthWithDelay) {
  auto r = Parse(
      "module t;\n"
      "  trireg (large) #(0, 0, 50) cap1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 4);
  EXPECT_EQ(item->name, "cap1");
  EXPECT_NE(item->net_delay_decay, nullptr);
}

TEST(DataTypeParsing, TriregNoChargeStrengthParserDefault) {
  auto r = Parse(
      "module t;\n"
      "  trireg a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 0);
}

TEST(DataTypeParsing, TriregChargeStrengthSignedVector) {
  auto r = Parse(
      "module t;\n"
      "  trireg (small) signed [3:0] cap2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 1);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_EQ(item->name, "cap2");
}

TEST(DataTypeParsing, TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2);
  EXPECT_EQ(item->name, "m");
}

// Only small/medium/large name a charge strength. A drive-strength keyword
// such as weak is not in the charge-strength set, so the parser declines to
// consume the parenthesized group and the declaration fails.
TEST(DataTypeParsing, DriveStrengthKeywordIsNotChargeStrength) {
  auto r = Parse(
      "module t;\n"
      "  trireg (weak) c;\n"
      "endmodule\n");
  // §6.7 owns the net declaration list, and that is where the declaration
  // fails: ParseChargeStrength puts the position back on the '(' it could not
  // read as small, medium or large, so no §6.3.2.1 report is written here.
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got '('", 2, "6.7"));
}

TEST(DataTypeParsing, ChargeStrengthKeywordOnWireFails) {
  auto r = Parse(
      "module t;\n"
      "  wire (small) w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

constexpr const char* kChargeStrengthRule =
    "charge strength can only be used with trireg nets";

// §6.3.2.1 keeps a charge strength to trireg nets, so every other built-in net
// type is reported with each of the three sizes, while the trireg declared the
// same way beside it parses clean.
TEST(DataTypeParsing, ChargeStrengthOnEveryOtherNetTypeIsReported) {
  for (const char* net_type : {"tri", "wand", "wor", "triand", "trior", "tri0",
                               "tri1", "uwire", "supply0", "supply1"}) {
    for (const char* size : {"small", "medium", "large"}) {
      auto r = Parse(
          std::format("module t;\n  {} ({}) n;\nendmodule\n", net_type, size));
      EXPECT_TRUE(ReportedError(r.diags, kChargeStrengthRule, 2, "6.3.2.1"))
          << net_type << " (" << size << ")";
    }
  }
}

TEST(DataTypeParsing, ChargeStrengthOnATriregOfEachSizeIsAccepted) {
  for (const char* size : {"small", "medium", "large"}) {
    auto r =
        Parse(std::format("module t;\n  trireg ({}) n;\nendmodule\n", size));
    EXPECT_FALSE(r.has_errors) << size;
  }
}

// A vector, a data type and a list of declarators after the strength leave the
// net type what decides the rule.
TEST(DataTypeParsing, ChargeStrengthOnAVectorOrListOfOtherNetsIsReported) {
  auto vec = Parse(
      "module t;\n"
      "  tri (large) [3:0] v;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(vec.diags, kChargeStrengthRule, 2, "6.3.2.1"));
  auto list = Parse(
      "module t;\n"
      "  wand (small) logic a, b;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(list.diags, kChargeStrengthRule, 2, "6.3.2.1"));
  auto trireg = Parse(
      "module t;\n"
      "  trireg (large) logic [3:0] v, w;\n"
      "endmodule\n");
  EXPECT_FALSE(trireg.has_errors);
}

std::ptrdiff_t ErrorsIn(const std::vector<Diagnostic>& diags) {
  return std::count_if(diags.begin(), diags.end(), [](const Diagnostic& d) {
    return d.severity == DiagSeverity::kError;
  });
}

// A net of a user-defined nettype is no trireg either, so its charge strength
// is reported under §6.3.2.1, once, where the declarator would otherwise stop
// at the parenthesis.
TEST(DataTypeParsing, ChargeStrengthOnANettypeNetIsReported) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [1:0] nt;\n"
      "  nt (small) n;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kChargeStrengthRule, 3, "6.3.2.1"));
  EXPECT_EQ(ErrorsIn(r.diags), 1);
}

// Syntax 6-2 in §6.7 gives a nettype's net a delay and no strength, so a drive
// strength there is reported once under §6.7, with or without an assignment,
// while the same net with its delay alone parses clean.
TEST(DataTypeParsing, DriveStrengthOnANettypeNetIsReported) {
  for (const char* decl :
       {"nt (strong0, weak1) n = 2'b01;", "nt (pull1, highz0) n;"}) {
    auto r = Parse(std::format(
        "module t;\n  nettype logic [1:0] nt;\n  {}\nendmodule\n", decl));
    EXPECT_TRUE(ReportedError(
        r.diags, "a net of a user-defined nettype takes no drive strength", 3,
        "6.7"))
        << decl;
    EXPECT_EQ(ErrorsIn(r.diags), 1) << decl;
  }
  for (const char* decl : {"nt n;", "nt #5 n = 2'b01;"}) {
    auto r = Parse(std::format(
        "module t;\n  nettype logic [1:0] nt;\n  {}\nendmodule\n", decl));
    EXPECT_FALSE(r.has_errors) << decl;
  }
}

// A net type keyword keeps its drive strength, with nothing reported, so the
// report above belongs to the nettype and not to every strength the
// declaration list reads.
TEST(DataTypeParsing, DriveStrengthOnANetTypeKeywordIsAccepted) {
  auto r = Parse(
      "module t;\n"
      "  wire (strong0, weak1) [1:0] w = 2'b01;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->drive_strength0, 0);
  EXPECT_NE(item->drive_strength1, 0);
}

// The rule holds wherever a net may be declared: in an interface, a program, a
// generate block of either kind, a nested module and the compilation unit.
TEST(DataTypeParsing, ChargeStrengthOnAWireIsReportedInEveryPlace) {
  struct Place {
    const char* open;
    const char* close;
    uint32_t line;
  };
  for (const Place& p : {
           Place{"interface i;\n", "endinterface\n", 2},
           Place{"program p;\n", "endprogram\n", 2},
           Place{"module m;\n  if (1) begin : g\n", "  end\nendmodule\n", 3},
           Place{"module m;\n  for (genvar k = 0; k < 2; k++) begin : g\n",
                 "  end\nendmodule\n", 3},
           Place{"module m;\n  module inner;\n", "  endmodule\nendmodule\n", 3},
           Place{"", "", 1},
       }) {
    auto wire = Parse(std::format("{}  wire (small) w;\n{}", p.open, p.close));
    EXPECT_TRUE(
        ReportedError(wire.diags, kChargeStrengthRule, p.line, "6.3.2.1"))
        << p.open;
    auto trireg =
        Parse(std::format("{}  trireg (small) t;\n{}", p.open, p.close));
    EXPECT_FALSE(trireg.has_errors) << p.open;
  }
}

}  // namespace
