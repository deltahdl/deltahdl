#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "synthesis/mem_infer.h"

using namespace delta;

// --- Test fixture ---

struct MemInferFixture {
  SourceManager src_mgr;
  DiagEngine diag{src_mgr};
  Arena arena;
};

static const RtlirModule *ElaborateSrc(MemInferFixture &f,
                                       const std::string &src) {
  auto fid = f.src_mgr.AddFile("<test>", src);
  Lexer lexer(f.src_mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  if (!design || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// =============================================================================
// Single-port write pattern: mem[addr] <= wdata inside always_ff
// =============================================================================

TEST(MemInfer, DetectSinglePortWrite) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] addr,\n"
                           "         input logic [7:0] wdata, input we);\n"
                           "  logic [7:0] mem;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    if (we) mem[addr] <= wdata;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].name, "mem");
}

TEST(MemInfer, DetectSinglePortWrite_PortDetails) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] addr,\n"
                           "         input logic [7:0] wdata, input we);\n"
                           "  logic [7:0] mem;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    if (we) mem[addr] <= wdata;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].write_ports.size(), 1u);
  EXPECT_TRUE(memories[0].write_ports[0].is_write);
  EXPECT_EQ(memories[0].write_ports[0].clock_edge, Edge::kPosedge);
}

// =============================================================================
// Single-port read pattern: rdata <= mem[addr] inside always_ff
// =============================================================================

TEST(MemInfer, DetectSinglePortRead) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] addr,\n"
                           "         output logic [7:0] rdata);\n"
                           "  logic [7:0] mem;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    rdata <= mem[addr];\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].name, "mem");
}

TEST(MemInfer, DetectSinglePortRead_PortDetails) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] addr,\n"
                           "         output logic [7:0] rdata);\n"
                           "  logic [7:0] mem;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    rdata <= mem[addr];\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].read_ports.size(), 1u);
  EXPECT_FALSE(memories[0].read_ports[0].is_write);
  EXPECT_EQ(memories[0].read_ports[0].clock_edge, Edge::kPosedge);
}

// =============================================================================
// Dual-port (read + write) detection in same always_ff block
// =============================================================================

TEST(MemInfer, DetectDualPort) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] raddr,\n"
                           "         input logic [3:0] waddr,\n"
                           "         input logic [7:0] wdata, input we,\n"
                           "         output logic [7:0] rdata);\n"
                           "  logic [7:0] mem;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    rdata <= mem[raddr];\n"
                           "    if (we) mem[waddr] <= wdata;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].name, "mem");
  EXPECT_EQ(memories[0].read_ports.size(), 1u);
  EXPECT_EQ(memories[0].write_ports.size(), 1u);
}

// =============================================================================
// No memory when no array patterns (scalar assignments only)
// =============================================================================

TEST(MemInfer, NoMemoryForScalarAssign) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input d, output reg q);\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    q <= d;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  EXPECT_TRUE(memories.empty());
}

// =============================================================================
// ROM inference: read-only array access (no writes)
// =============================================================================

TEST(MemInfer, RomInference) {
  MemInferFixture f;
  auto *mod = ElaborateSrc(f,
                           "module m(input clk, input logic [3:0] addr,\n"
                           "         output logic [7:0] rdata);\n"
                           "  logic [7:0] rom;\n"
                           "  always_ff @(posedge clk) begin\n"
                           "    rdata <= rom[addr];\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);

  auto memories = InferMemories(mod);
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(memories[0].name, "rom");
  EXPECT_EQ(memories[0].read_ports.size(), 1u);
  EXPECT_TRUE(memories[0].write_ports.empty());
}
