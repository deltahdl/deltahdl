#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult28b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult28b Parse(const std::string& src) {
  ParseResult28b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =============================================================================
// LRM section 28.12 -- Specify blocks
// =============================================================================

// --- Empty specify block ---

TEST(ParserSection28, Sec28_12_EmptySpecifyBlock) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_spec = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      found_spec = true;
      EXPECT_EQ(item->specify_items.size(), 0u);
    }
  }
  EXPECT_TRUE(found_spec);
}

// --- Conditional path: if (cond) (a => b) = delay ---

TEST(ParserSection28, Sec28_12_ConditionalPath) {
  auto r = Parse(
      "module m(input a, en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
      EXPECT_NE(si->path.condition, nullptr);
      EXPECT_FALSE(si->path.is_ifnone);
      ASSERT_EQ(si->path.src_ports.size(), 1u);
      EXPECT_EQ(si->path.src_ports[0], "a");
      ASSERT_EQ(si->path.dst_ports.size(), 1u);
      EXPECT_EQ(si->path.dst_ports[0], "b");
      ASSERT_EQ(si->path.delays.size(), 1u);
    }
  }
}

// --- Ifnone path ---

TEST(ParserSection28, Sec28_12_IfnonePath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      EXPECT_TRUE(si->path.is_ifnone);
      EXPECT_EQ(si->path.condition, nullptr);
      ASSERT_EQ(si->path.delays.size(), 1u);
    }
  }
}

// --- Edge-sensitive paths ---

TEST(ParserSection28, Sec28_12_PosedgeSensitivePath) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
      ASSERT_EQ(si->path.src_ports.size(), 1u);
      EXPECT_EQ(si->path.src_ports[0], "clk");
      ASSERT_EQ(si->path.dst_ports.size(), 1u);
      EXPECT_EQ(si->path.dst_ports[0], "q");
    }
  }
}

TEST(ParserSection28, Sec28_12_NegedgeSensitivePath) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (negedge clk => q) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
      ASSERT_EQ(si->path.src_ports.size(), 1u);
      EXPECT_EQ(si->path.src_ports[0], "clk");
    }
  }
}

// --- Multiple source/destination ports ---

TEST(ParserSection28, Sec28_12_MultipleSourceDestPorts) {
  auto r = Parse(
      "module m(input a, b, c, output x, y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
      ASSERT_EQ(si->path.src_ports.size(), 3u);
      EXPECT_EQ(si->path.src_ports[0], "a");
      EXPECT_EQ(si->path.src_ports[1], "b");
      EXPECT_EQ(si->path.src_ports[2], "c");
      ASSERT_EQ(si->path.dst_ports.size(), 2u);
      EXPECT_EQ(si->path.dst_ports[0], "x");
      EXPECT_EQ(si->path.dst_ports[1], "y");
    }
  }
}

// --- Delay specifications ---

TEST(ParserSection28, Sec28_12_TwoDelayPath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (5, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
      ASSERT_EQ(si->path.delays.size(), 2u);
    }
  }
}

TEST(ParserSection28, Sec28_12_ThreeDelayPath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (3, 7, 11);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      ASSERT_EQ(si->path.delays.size(), 3u);
    }
  }
}

TEST(ParserSection28, Sec28_12_SixDelayPath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      ASSERT_EQ(si->path.delays.size(), 6u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TwelveDelayPath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      ASSERT_EQ(si->path.delays.size(), 12u);
    }
  }
}

// --- Multiple paths in one specify block ---

TEST(ParserSection28, Sec28_12_MultiplePathsInSpecifyBlock) {
  auto r = Parse(
      "module m(input a, b, output x, y);\n"
      "  specify\n"
      "    (a => x) = 5;\n"
      "    (b => y) = 7;\n"
      "    (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 3u);
      for (auto* si : item->specify_items) {
        EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
        EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
      }
    }
  }
}

// --- Specparam with min:typ:max ---

TEST(ParserSection28, Sec28_12_SpecparamMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify\n"
              "    specparam tPLH = 3:5:7;\n"
              "    (a => b) = tPLH;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// --- Pulsestyle declarations ---

TEST(ParserSection28, Sec28_12_PulsestyleOnevent) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    pulsestyle_onevent b;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPulsestyle);
      EXPECT_FALSE(si->is_ondetect);
      ASSERT_EQ(si->signal_list.size(), 1u);
      EXPECT_EQ(si->signal_list[0], "b");
    }
  }
}

TEST(ParserSection28, Sec28_12_PulsestyleOndetect) {
  auto r = Parse(
      "module m(input a, output b, c);\n"
      "  specify\n"
      "    pulsestyle_ondetect b, c;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kPulsestyle);
      EXPECT_TRUE(si->is_ondetect);
      ASSERT_EQ(si->signal_list.size(), 2u);
      EXPECT_EQ(si->signal_list[0], "b");
      EXPECT_EQ(si->signal_list[1], "c");
    }
  }
}

// --- Showcancelled and noshowcancelled ---

TEST(ParserSection28, Sec28_12_Showcancelled) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    showcancelled b;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kShowcancelled);
      EXPECT_FALSE(si->is_noshowcancelled);
      ASSERT_EQ(si->signal_list.size(), 1u);
      EXPECT_EQ(si->signal_list[0], "b");
    }
  }
}

TEST(ParserSection28, Sec28_12_Noshowcancelled) {
  auto r = Parse(
      "module m(input a, output b, c);\n"
      "  specify\n"
      "    noshowcancelled b, c;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kShowcancelled);
      EXPECT_TRUE(si->is_noshowcancelled);
      ASSERT_EQ(si->signal_list.size(), 2u);
    }
  }
}

// --- Timing checks ---

TEST(ParserSection28, Sec28_12_TimingCheckSetup) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNone);
      EXPECT_EQ(si->timing_check.ref_signal, "d");
      EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.data_signal, "clk");
      ASSERT_EQ(si->timing_check.limits.size(), 1u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckHold) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kHold);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
      EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
      EXPECT_EQ(si->timing_check.data_signal, "d");
      ASSERT_EQ(si->timing_check.limits.size(), 1u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckSetuphold) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, 3, 2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetuphold);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
      EXPECT_EQ(si->timing_check.data_signal, "d");
      ASSERT_EQ(si->timing_check.limits.size(), 2u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckRecovery) {
  auto r = Parse(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recovery(posedge clk, rst, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecovery);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
      EXPECT_EQ(si->timing_check.data_signal, "rst");
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckRemoval) {
  auto r = Parse(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $removal(negedge rst, posedge clk, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRemoval);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
      EXPECT_EQ(si->timing_check.ref_signal, "rst");
      EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.data_signal, "clk");
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckRecrem) {
  auto r = Parse(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 5, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecrem);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
      EXPECT_EQ(si->timing_check.data_signal, "rst");
      ASSERT_EQ(si->timing_check.limits.size(), 2u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckWidth) {
  auto r = Parse(
      "module m(input clk);\n"
      "  specify\n"
      "    $width(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kWidth);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
      ASSERT_EQ(si->timing_check.limits.size(), 1u);
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckPeriod) {
  auto r = Parse(
      "module m(input clk);\n"
      "  specify\n"
      "    $period(posedge clk, 100);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kPeriod);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk");
    }
  }
}

TEST(ParserSection28, Sec28_12_TimingCheckSkew) {
  auto r = Parse(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $skew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSkew);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.ref_signal, "clk1");
      EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.data_signal, "clk2");
    }
  }
}

// --- Timing check with notifier ---

TEST(ParserSection28, Sec28_12_TimingCheckWithNotifier) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  reg notif_reg;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, notif_reg);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
      EXPECT_EQ(si->timing_check.notifier, "notif_reg");
    }
  }
}

// --- Timing check with edge on both signals ---

TEST(ParserSection28, Sec28_12_TimingCheckWithEdges) {
  auto r = Parse(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(negedge d, posedge clk, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 1u);
      auto* si = item->specify_items[0];
      EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
      EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
      EXPECT_EQ(si->timing_check.ref_signal, "d");
      EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
      EXPECT_EQ(si->timing_check.data_signal, "clk");
    }
  }
}

// --- Multiple timing checks in one specify block ---

TEST(ParserSection28, Sec28_12_MultipleTimingChecksInSpecifyBlock) {
  auto r = Parse(
      "module m(input d, clk, rst);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "    $recovery(posedge clk, rst, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ASSERT_EQ(item->specify_items.size(), 3u);
      EXPECT_EQ(item->specify_items[0]->timing_check.check_kind,
                TimingCheckKind::kSetup);
      EXPECT_EQ(item->specify_items[1]->timing_check.check_kind,
                TimingCheckKind::kHold);
      EXPECT_EQ(item->specify_items[2]->timing_check.check_kind,
                TimingCheckKind::kRecovery);
    }
  }
}

// --- ParseOk-based tests for broader coverage ---

TEST(ParserSection28, Sec28_12_PosedgeFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input clk, output q, qb);\n"
              "  specify\n"
              "    (posedge clk *> q, qb) = (3, 5);\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ParserSection28, Sec28_12_ConditionalFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, b, en, output y);\n"
              "  specify\n"
              "    if (en) (a, b *> y) = 10;\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ParserSection28, Sec28_12_MixedPathsAndTimingChecks) {
  EXPECT_TRUE(
      ParseOk("module m(input a, d, clk, output b);\n"
              "  specify\n"
              "    specparam tPD = 10;\n"
              "    (a => b) = tPD;\n"
              "    $setup(d, posedge clk, 5);\n"
              "    $hold(posedge clk, d, 3);\n"
              "    showcancelled b;\n"
              "    pulsestyle_onevent b;\n"
              "  endspecify\n"
              "endmodule\n"));
}
