#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

struct KeywordCase {
  const char* keyword;
  const char* terminals;
  GateKind kind;
};

constexpr KeywordCase kCases[] = {
    {"and", "(o, a, b)", GateKind::kAnd},
    {"nand", "(o, a, b)", GateKind::kNand},
    {"or", "(o, a, b)", GateKind::kOr},
    {"nor", "(o, a, b)", GateKind::kNor},
    {"xor", "(o, a, b)", GateKind::kXor},
    {"xnor", "(o, a, b)", GateKind::kXnor},
    {"buf", "(o, a)", GateKind::kBuf},
    {"not", "(o, a)", GateKind::kNot},
    {"bufif0", "(o, a, c)", GateKind::kBufif0},
    {"bufif1", "(o, a, c)", GateKind::kBufif1},
    {"notif0", "(o, a, c)", GateKind::kNotif0},
    {"notif1", "(o, a, c)", GateKind::kNotif1},
    {"pulldown", "(o)", GateKind::kPulldown},
    {"pullup", "(o)", GateKind::kPullup},
    {"cmos", "(o, a, nc, pc)", GateKind::kCmos},
    {"rcmos", "(o, a, nc, pc)", GateKind::kRcmos},
    {"nmos", "(o, a, g)", GateKind::kNmos},
    {"pmos", "(o, a, g)", GateKind::kPmos},
    {"rnmos", "(o, a, g)", GateKind::kRnmos},
    {"rpmos", "(o, a, g)", GateKind::kRpmos},
    {"tran", "(a, b)", GateKind::kTran},
    {"rtran", "(a, b)", GateKind::kRtran},
    {"tranif0", "(a, b, c)", GateKind::kTranif0},
    {"tranif1", "(a, b, c)", GateKind::kTranif1},
    {"rtranif0", "(a, b, c)", GateKind::kRtranif0},
    {"rtranif1", "(a, b, c)", GateKind::kRtranif1},
};

TEST(GateKeywordOpensDeclaration, AllTwentySixTableEntries) {
  for (const auto& c : kCases) {
    std::string src = std::string("module m;\n  ") + c.keyword + " " +
                      c.terminals + ";\nendmodule\n";
    auto r = Parse(src);
    ASSERT_NE(r.cu, nullptr) << "keyword: " << c.keyword;
    EXPECT_FALSE(r.has_errors) << "keyword: " << c.keyword;
    auto* g = FindGateByKind(r.cu->modules[0]->items, c.kind);
    ASSERT_NE(g, nullptr) << "keyword: " << c.keyword;
    EXPECT_EQ(g->gate_kind, c.kind) << "keyword: " << c.keyword;
  }
}

TEST(GateKeywordOpensDeclaration, NonKeywordIsNotGateDecl) {
  auto r = Parse("module m;\n  notagate (o, a, b);\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  for (auto* item : r.cu->modules[0]->items) {
    EXPECT_NE(item->kind, ModuleItemKind::kGateInst);
  }
}

// §28.3.1's "a declaration begins with the primitive keyword" rule is not tied
// to the top-level module-item position: a gate instantiation is a
// module-or-generate item, so the same keyword must open a declaration inside a
// generate block too. Drive a gate through the body of a generate-if and
// confirm the keyword still yields a gate instance in that syntactic position.
TEST(GateKeywordOpensDeclaration, InsideGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter p = 1;\n"
      "  if (p) begin : g\n"
      "    and (o, a, b);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen, nullptr);
  auto* g = FindGateByKind(gen->gen_body, GateKind::kAnd);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_kind, GateKind::kAnd);
}

}  // namespace
