#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_identifier_positions.h"
#include "model_keyword_tables.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {
TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is included from Table 22-1 and stays reserved";
  }
}

TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kVerilog2001AddedKeywords), 21u);
  for (const char* word : kVerilog2001AddedKeywords) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is included from Table 22-2 and is reserved here";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(VarDecl(word))))
        << word << " is an addition of the later of the two included lists";
  }
}

TEST(CompilerDirectiveParsing,
     Verilog2005ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1364-2005", {"wire", "generate", "uwire"},
      {"design element", "port", "instance", "task", "named block"});
}

TEST(CompilerDirectiveParsing,
     Verilog2005UnlistedWordsFillEveryIdentifierPosition) {
  ExpectUnlistedWordsNameEveryEntity("1364-2005", {"logic", "bit"});
}

TEST(CompilerDirectiveParsing, Verilog2005ReservesTheWordItAddsItself) {
  ASSERT_EQ(std::size(kVerilog2005AddedKeywords), 1u);
  const char* added = kVerilog2005AddedKeywords[0];

  auto here = ParseWithPreprocessor(In2005(VarDecl(added)));
  EXPECT_TRUE(ReportedError(
      here.diags, std::string("expected identifier, got '") + added + "'",
      LineInRegion(2), "6.8"));

  for (const auto& earlier : {In2001(VarDecl(added)), In1995(VarDecl(added))}) {
    auto r = ParseWithPreprocessor(earlier);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    ASSERT_EQ(r.cu->modules.size(), 1u);
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, added));
  }
}

TEST(CompilerDirectiveParsing, Verilog2005AddedWordOpensANetDeclaration) {
  auto r = ParseWithPreprocessor(
      In2005("module m (input wire [7:0] a, output uwire [7:0] y);\n"
             "  uwire        scalar_net;\n"
             "  uwire [3:0]  vector_net;\n"
             "  uwire signed [7:0] signed_net;\n"
             "  assign y = a;\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(m->ports[1].data_type.kind, DataTypeKind::kUwire);

  const char* const kNets[] = {"scalar_net", "vector_net", "signed_net"};
  for (const char* name : kNets) {
    bool found = false;
    for (auto* item : m->items) {
      if (item->kind != ModuleItemKind::kNetDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  bool signed_seen = false;
  for (auto* item : m->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "signed_net") {
      EXPECT_TRUE(item->data_type.is_signed);
      signed_seen = true;
    }
  }
  EXPECT_TRUE(signed_seen);

  auto earlier =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  uwire scalar_net;\n"
                                   "endmodule\n"));
  ASSERT_NE(earlier.cu, nullptr);
  auto* earlier_item = earlier.cu->modules[0]->items[0];
  EXPECT_EQ(earlier_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(earlier_item->data_type.type_name, "uwire");
  EXPECT_TRUE(earlier_item->type_name_undeclared_at_parse);
}

TEST(CompilerDirectiveParsing, Verilog2005AddedWordTypesEveryDeclarationForm) {
  auto with_assignment =
      ParseWithPreprocessor(In2005("module m;\n"
                                   "  reg   [7:0] src;\n"
                                   "  uwire [7:0] bus = src + 8'd1;\n"
                                   "endmodule\n"));
  ASSERT_NE(with_assignment.cu, nullptr);
  EXPECT_FALSE(with_assignment.has_errors);
  bool bus_seen = false;
  for (auto* item : with_assignment.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNetDecl || item->name != "bus") continue;
    bus_seen = true;
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
    EXPECT_NE(item->init_expr, nullptr);
  }
  EXPECT_TRUE(bus_seen);

  auto non_ansi =
      ParseWithPreprocessor(In2005("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  uwire  [7:0] y;\n"
                                   "  assign y = a;\n"
                                   "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* ch = non_ansi.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : ch->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  auto assigned =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg   [7:0] src;\n"
                                   "  uwire [7:0] bus = src + 8'd1;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(assigned.diags, "expected ';', got '['",
                            LineInRegion(3), "6.8"));

  auto in_body =
      ParseWithPreprocessor(In2001("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  uwire  [7:0] y;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(in_body.diags, "expected ';', got '['",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing, Verilog2005AddedWordNamesEntitiesUnderEarlier) {
  ExpectWordsNameEntitiesUnder("1364-2001", "1364-2005", {"uwire"},
                               {"design element", "port", "instance", "task",
                                "function", "gate instance", "genvar"});

  auto named_module = ParseWithPreprocessor(
      In2001(AtPosition(kIdentifierPositions[0], "uwire")));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "uwire");

  auto named_instance = ParseWithPreprocessor(
      In2001(AtPosition(kIdentifierPositions[2], "uwire")));
  ASSERT_NE(named_instance.cu, nullptr);
  ASSERT_EQ(named_instance.cu->modules.size(), 2u);
  auto* inst = FindItemByKind(named_instance.cu->modules[1]->items,
                              ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "uwire");
}

TEST(CompilerDirectiveParsing, Verilog2005IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1364-2005");
}

TEST(CompilerDirectiveParsing,
     Verilog2005IncludedAdditionsOpenTheirConstructs) {
  ExpectVerilog2001ConstructsParse("1364-2005");
}

TEST(CompilerDirectiveParsing, Verilog2005IncludedVerilog1995WordsStillWork) {
  ExpectVerilog1995ConstructsParse("1364-2005");
}

TEST(CompilerDirectiveParsing, Verilog2005LeavesUnlistedWordsAsIdentifiers) {
  const char* const kUnlisted[] = {"logic", "interface", "bit", "byte", "int"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    auto typed = ParseWithPreprocessor(In2005(as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace
