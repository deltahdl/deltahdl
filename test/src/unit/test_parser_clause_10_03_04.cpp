// §10.3.4: Continuous assignment strengths

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Drive strength in continuous assign context ---
TEST(ParserA222, DriveStrengthContinuousAssign) {
  // drive_strength used with assign statement
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, pull1) w = 1'b1;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  EXPECT_EQ(item->drive_strength0, 4u);  // strong0 = 4
  EXPECT_EQ(item->drive_strength1, 3u);  // pull1 = 3
}

static std::vector<ModuleItem*> FindUdpInsts(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> insts;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kUdpInst) insts.push_back(item);
  }
  return insts;
}

static std::vector<ModuleItem*> FindContAssigns(
    const std::vector<ModuleItem*>& items) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kContAssign) result.push_back(item);
  }
  return result;
}

static std::vector<ModuleItem*> FindItems(const std::vector<ModuleItem*>& items,
                                          ModuleItemKind kind) {
  std::vector<ModuleItem*> result;
  for (auto* item : items) {
    if (item->kind == kind) result.push_back(item);
  }
  return result;
}

TEST(ParserA601, ContinuousAssign_DriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 4u);
  EXPECT_EQ(cas[0]->drive_strength1, 2u);
}

TEST(ParserA601, ContinuousAssign_DriveStrengthReversed) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_EQ(cas[0]->drive_strength0, 5u);
  EXPECT_EQ(cas[0]->drive_strength1, 3u);
}

TEST(ParserA601, ContinuousAssign_StrengthAndDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (pull0, pull1) #5 a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto cas = FindContAssigns(r.cu->modules[0]->items);
  ASSERT_EQ(cas.size(), 1u);
  EXPECT_NE(cas[0]->drive_strength0, 0u);
  EXPECT_NE(cas[0]->drive_strength1, 0u);
  EXPECT_NE(cas[0]->assign_delay, nullptr);
}

struct ParseResult10b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10b Parse(const std::string& src) {
  ParseResult10b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// §10.3.4: Drive strength on continuous assignment.
TEST(ParserSection10, ContinuousAssignDriveStrength) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* ca = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ca = item;
      break;
    }
  }
  ASSERT_NE(ca, nullptr);
  // 4=strong, 2=weak (parser encoding:
  // 0=none,1=highz,2=weak,3=pull,4=strong,5=supply)
  EXPECT_EQ(ca->drive_strength0, 4u);
  EXPECT_EQ(ca->drive_strength1, 2u);
}

// §10.3.4: Drive strength order can be reversed.
TEST(ParserSection10, ContinuousAssignDriveStrengthReversed) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign (pull1, supply0) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ModuleItem* ca = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ca = item;
      break;
    }
  }
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(ca->drive_strength0, 5u);  // supply0
  EXPECT_EQ(ca->drive_strength1, 3u);  // pull1
}

}  // namespace
