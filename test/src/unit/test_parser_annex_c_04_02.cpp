#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(ProceduralAssignDeassignPlacement, BothFormsInTheirPlacesAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    assign b = a;\n"
      "    deassign b;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign));
}

TEST(ProceduralAssignDeassignPlacement, DeassignOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  deassign a;\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'deassign' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

TEST(ProceduralAssignDeassignPlacement, ForceOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  force a = 1'b1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'force' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
}

TEST(ProceduralAssignDeassignPlacement, ReleaseOutsideAProcedureIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  logic a;\n"
      "  release a;\n"
      "  int x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'release' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kVarDecl));
}

TEST(ProceduralAssignDeassignPlacement,
     DeassignOutsideAProcedureInAnInterface) {
  auto r = Parse(
      "interface i;\n"
      "  logic a;\n"
      "  deassign a;\n"
      "endinterface\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'deassign' is a procedural continuous assignment "
                            "statement and is placed within a procedure",
                            3, "C.4.2"));
}

std::string Substituted(std::string src, const std::string& stmt) {
  src.replace(src.find('%'), 1, stmt);
  return src;
}

constexpr const char* kPlacementReport =
    "is a procedural continuous assignment statement and is placed within a "
    "procedure";

const char* const kProceduralStatements[] = {"deassign a;", "force a = 1'b1;",
                                             "release a;"};

void ExpectEachStatementReportedIn(const char* const* places, size_t count) {
  for (size_t i = 0; i < count; ++i) {
    for (const char* stmt : kProceduralStatements) {
      const std::string kSrc = Substituted(places[i], stmt);
      auto r = Parse(kSrc);
      std::string keyword(stmt, std::string_view(stmt).find(' '));
      std::string message = "'";
      message += keyword;
      message += "' ";
      message += kPlacementReport;
      EXPECT_TRUE(
          ReportedError(r.diags, message, LineHolding(kSrc, keyword), "C.4.2"))
          << kSrc;
    }
  }
}

TEST(ProceduralAssignDeassignPlacement,
     EachStatementOutsideAProcedureIsRejected) {
  const char* const kPlaces[] = {
      "module m;\n  logic a;\n  %\nendmodule\n",
      "interface i;\n  logic a;\n  %\nendinterface\n",
      "program p;\n  logic a;\n  %\nendprogram\n",
      "checker c;\n  logic a;\n  %\nendchecker\n",
      "package pk;\n  logic a;\n  %\nendpackage\n",
      "module m;\n  logic a;\n  if (1) begin : g\n    %\n  end\nendmodule\n",
      "module m;\n  logic a;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n    %\n  end\nendmodule\n",
      "module m;\n  logic a;\n"
      "  case (1)\n    1: begin : g\n      %\n    end\n  endcase\nendmodule\n",
  };
  ExpectEachStatementReportedIn(kPlaces, std::size(kPlaces));
}

TEST(ProceduralAssignDeassignPlacement,
     DISABLED_EachStatementInTheUnitScopeOrAClassBodyIsRejected) {
  const char* const kPlaces[] = {
      "logic a;\n%\nmodule m; endmodule\n",
      "class c;\n  logic a;\n  %\nendclass\n",
  };
  ExpectEachStatementReportedIn(kPlaces, std::size(kPlaces));
}

TEST(ProceduralAssignDeassignPlacement, EachStatementInAProcedureIsAccepted) {
  const char* const kPlaces[] = {
      "interface i;\n  logic a;\n  initial begin\n    %\n  end\nendinterface\n",
      "program p;\n  logic a;\n  initial begin\n    %\n  end\nendprogram\n",
      "module m;\n  logic a;\n  if (1) begin : g\n"
      "    initial begin\n      %\n    end\n  end\nendmodule\n",
      "module m;\n  logic a;\n  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    initial begin\n      %\n    end\n  end\nendmodule\n",
      "module m;\n  logic a;\n  task t;\n    %\n  endtask\nendmodule\n",
      "package pk;\n  logic a;\n  task t;\n    %\n  endtask\nendpackage\n",
      "class c;\n  logic a;\n  task t;\n    %\n  endtask\nendclass\n",
  };
  for (const char* place : kPlaces) {
    for (const char* stmt : kProceduralStatements) {
      const std::string kSrc = Substituted(place, stmt);
      auto r = Parse(kSrc);
      EXPECT_FALSE(r.has_errors) << kSrc;
    }
  }
}

}  // namespace
