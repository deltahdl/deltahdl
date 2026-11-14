#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(SourceText, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->modules[0]->items[0]->init_expr, nullptr);
}

TEST(SourceText, DefaultDisableIffInGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  bit rst;\n"
      "  if (1) begin\n"
      "    default disable iff rst;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* gen = nullptr;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kGenerateIf) {
      gen = it;
      break;
    }
  }
  ASSERT_NE(gen, nullptr);
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(gen->gen_body[0]->init_expr, nullptr);
}

TEST(SourceText, DefaultDisableIffInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  default disable iff rst;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->interfaces[0]->items[0]->init_expr, nullptr);
}

TEST(SourceText, DefaultDisableIffInProgram) {
  auto r = Parse(
      "program p;\n"
      "  default disable iff rst;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
  EXPECT_NE(r.cu->programs[0]->items[0]->init_expr, nullptr);
}

TEST(DefaultDisableIff, MalformedDefaultDisableNames16_15) {
  auto r = Parse(
      "module m;\n"
      "  default disable x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'iff'", 2, "16.15"));
}

struct DeclarationPlace {
  const char* name;
  const char* head;
  const char* tail;
};

constexpr DeclarationPlace kPlaces[] = {
    {"module", "module m;\n  bit rst, rst_n, en;\n", "endmodule\n"},
    {"interface", "interface w;\n  bit rst, rst_n, en;\n", "endinterface\n"},
    {"program", "program w;\n  bit rst, rst_n, en;\n", "endprogram\n"},
    {"checker", "checker w;\n  bit rst, rst_n, en;\n", "endchecker\n"},
    {"generate block", "module m;\n  bit rst, rst_n, en;\n  if (1) begin\n",
     "  end\nendmodule\n"},
};

void ExpectAcceptedInEachPlace(const std::string& declaration) {
  for (const DeclarationPlace& place : kPlaces) {
    auto r = Parse(std::string(place.head) + declaration + place.tail);
    EXPECT_FALSE(r.has_errors) << place.name << ": " << declaration;
  }
}

TEST(DefaultDisableIff, ABinaryOperatorOperandIsAcceptedInEachPlace) {
  ExpectAcceptedInEachPlace("  default disable iff !rst_n && en;\n");
}

TEST(DefaultDisableIff, DISABLED_ADistOperandIsAcceptedInEachPlace) {
  ExpectAcceptedInEachPlace(
      "  default disable iff rst dist {0 := 1, 1 := 1};\n");
  ExpectAcceptedInEachPlace(
      "  default disable iff rst dist {[0:3] :/ 1, default :/ 1};\n");
}

TEST(DefaultDisableIff, TheSameDistInAnAssertionsOwnClauseIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  bit clk, rst, a;\n"
      "  assert property (@(posedge clk) disable iff (rst dist {0 := 1, 1 := "
      "1})"
      " a);\n"
      "  assert property (@(posedge clk)\n"
      "    disable iff (rst dist {[0:3] :/ 1, default :/ 1}) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(DefaultDisableIff, AMissingSemicolonInAModuleIsReported) {
  auto r = Parse(
      "module m;\n"
      "  bit rst;\n"
      "  default disable iff rst\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 4, "16.15"));
}

TEST(DefaultDisableIff, TheTerminatedDeclarationInAModuleIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  bit rst;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(DefaultDisableIffPlacement, LoopCaseAndRegionGenerateBlocksAccept) {
  for (const char* src :
       {"module m;\n  bit rst;\n  for (genvar i = 0; i < 2; i++) begin : g\n"
        "    default disable iff rst;\n  end\nendmodule\n",
        "module m;\n  bit rst;\n  case (1)\n    1: begin : g\n"
        "      default disable iff rst;\n    end\n  endcase\nendmodule\n",
        "module m;\n  bit rst;\n  generate\n    default disable iff rst;\n"
        "  endgenerate\nendmodule\n"}) {
    auto r = Parse(src);
    EXPECT_FALSE(r.has_errors) << src;
  }
}

TEST(DefaultDisableIffPlacement, NestedInterfaceAndProgramDeclarationsAccept) {
  auto r = Parse(
      "module m;\n"
      "  interface ni;\n"
      "    bit rst;\n"
      "    default disable iff rst;\n"
      "  endinterface\n"
      "  program np;\n"
      "    bit rst;\n"
      "    default disable iff rst;\n"
      "  endprogram\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

struct MisplacedDeclaration {
  const char* place;
  const char* src;
  uint32_t line;
};

constexpr const char* kPlacementMessage = "a default disable iff declaration";

TEST(DefaultDisableIffPlacement,
     DISABLED_OutsideADesignElementOrGenerateBlockIsReportedOnce) {
  const MisplacedDeclaration kCases[] = {
      {"compilation unit", "bit rst;\ndefault disable iff rst;\n", 2},
      {"class", "class C;\n  bit rst;\n  default disable iff rst;\nendclass\n",
       3},
      {"function",
       "module m;\n  bit rst;\n  function void f();\n"
       "    default disable iff rst;\n  endfunction\nendmodule\n",
       4},
      {"task",
       "module m;\n  bit rst;\n  task t();\n"
       "    default disable iff rst;\n  endtask\nendmodule\n",
       4},
      {"initial procedure",
       "module m;\n  bit rst;\n  initial begin\n"
       "    default disable iff rst;\n  end\nendmodule\n",
       4},
      {"always procedure",
       "module m;\n  bit clk, rst;\n  always @(posedge clk) begin\n"
       "    default disable iff rst;\n  end\nendmodule\n",
       4},
      {"clocking block",
       "module m;\n  bit clk, rst;\n  clocking cb @(posedge clk);\n"
       "    default disable iff rst;\n  endclocking\nendmodule\n",
       4},
  };
  for (const MisplacedDeclaration& c : kCases) {
    auto r = Parse(c.src);
    EXPECT_TRUE(ReportedError(r.diags, kPlacementMessage, c.line, "16.15"))
        << c.place;
    size_t errors = 0;
    for (const Diagnostic& d : r.diags) {
      if (d.severity == DiagSeverity::kError) ++errors;
    }
    EXPECT_EQ(errors, 1u) << c.place;
  }
}

}  // namespace
