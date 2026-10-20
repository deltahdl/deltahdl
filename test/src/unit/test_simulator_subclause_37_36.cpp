#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_sealed_design_run.h"
#include "parser/ast_specify.h"
#include "preprocessor/protect_processing.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.36 "UDP": the VPI object model for a UDP definition (the "udp defn"
// node), its io decl, table entry, and initial children, and the table entry's
// own size and value. The udp instance and the udp -> udp defn edge belong to
// the neighboring §37.35 (Primitive, prim term); this clause owns the udp
// defn's properties and the two numbered Details.
//
//   defn vpiDefName  - the definition name a udp defn reports (string
//   dispatch). defn vpiSize     - the number of inputs (the shared kVpiSize
//   dispatch). defn vpiProtected- the protection flag every object carries
//   (§37.3.6). defn vpiPrimType - the primitive type; Detail 2 fixes vpiSeqPrim
//   for a
//                      sequential UDP and vpiCombPrim for a combinational one.
//   defn -> io decl / table entry / initial - one-to-many/one-to-one traversals
//                      served by the generic child walk.
//   table entry vpiSize - the number of symbol entries (shared size dispatch).
//   table entry value   - Detail 1 allows only a string (decompilation) and a
//                      vector (ASCII symbol values) through vpi_get_value().
//
// The fixture installs a context so the public vpi_* entry points run their
// real dispatch, and provides the simulation plumbing a table-entry value read
// needs.
class UdpModel : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // A bare context-owned object of the requested kind, stamped with the name
  // the test wants - the same approach the §37.37 model tests use.
  VpiHandle MakeObject(int type, std::string_view name) {
    VpiHandle obj = vpi_ctx_.CreateModule(name, std::string(name));
    obj->type = type;
    return obj;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// C1: a udp defn reports its definition name - the UDP declaration's identifier
// - through vpi_get_str(vpiDefName).
TEST_F(UdpModel, DefinitionNameReportsUdpName) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "latch_udp");
  EXPECT_STREQ(vpi_get_str(vpiDefName, VpiHandleOf(defn)), "latch_udp");
}

// C2: a udp defn reports its number of inputs through vpiSize, which the shared
// size dispatch hands back from the stored size.
TEST_F(UdpModel, SizeReportsNumberOfInputs) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "mux_udp");
  defn->size = 3;  // a three-input UDP
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(defn)), 3);
}

// C3: a udp defn carries the vpiProtected Boolean (§37.3.6), TRUE when it
// stands for protected code and FALSE otherwise. §37.3.6 lets this property
// through even for a protected object.
TEST_F(UdpModel, ProtectedFlagReported) {
  VpiHandle open_defn = MakeObject(vpiUdpDefn, "open_udp");
  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(open_defn)), 0);

  VpiHandle sealed_defn = MakeObject(vpiUdpDefn, "sealed_udp");
  sealed_defn->is_protected = true;
  EXPECT_EQ(vpi_get(vpiIsProtected, VpiHandleOf(sealed_defn)), 1);
}

// C4 / Detail 2: a sequential UDP reports vpiSeqPrim through vpiPrimType.
TEST_F(UdpModel, PrimTypeReportsSequentialUdp) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "ff_udp");
  defn->prim_type = vpiSeqPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(defn)), vpiSeqPrim);
}

// C4 / Detail 2: a combinational UDP reports vpiCombPrim through vpiPrimType.
TEST_F(UdpModel, PrimTypeReportsCombinationalUdp) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "and_udp");
  defn->prim_type = vpiCombPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, VpiHandleOf(defn)), vpiCombPrim);
}

// C5: iterating vpiIODecl from a udp defn walks its io decl children (the UDP's
// output and input port declarations), in order.
TEST_F(UdpModel, TraversesToIoDecls) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "io_udp");
  VpiHandle out = MakeObject(vpiIODecl, "q");
  VpiHandle in0 = MakeObject(vpiIODecl, "a");
  VpiHandle in1 = MakeObject(vpiIODecl, "b");
  defn->children.push_back(out);
  defn->children.push_back(in0);
  defn->children.push_back(in1);

  vpiHandle iter = vpi_iterate(vpiIODecl, VpiHandleOf(defn));
  ASSERT_NE(iter, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle d = vpi_scan(iter)) seen.push_back(d);
  ASSERT_EQ(static_cast<int>(seen.size()), 3);
  EXPECT_EQ(VpiObjectOf(seen[0]), out);
  EXPECT_EQ(VpiObjectOf(seen[1]), in0);
  EXPECT_EQ(VpiObjectOf(seen[2]), in1);
}

// C6: iterating vpiTableEntry from a udp defn walks the rows of its state
// table.
TEST_F(UdpModel, TraversesToTableEntries) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "tab_udp");
  VpiHandle row0 = MakeObject(vpiTableEntry, "r0");
  VpiHandle row1 = MakeObject(vpiTableEntry, "r1");
  defn->children.push_back(row0);
  defn->children.push_back(row1);

  vpiHandle iter = vpi_iterate(vpiTableEntry, VpiHandleOf(defn));
  ASSERT_NE(iter, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle r = vpi_scan(iter)) seen.push_back(r);
  ASSERT_EQ(static_cast<int>(seen.size()), 2);
  EXPECT_EQ(VpiObjectOf(seen[0]), row0);
  EXPECT_EQ(VpiObjectOf(seen[1]), row1);
}

// C7: vpi_handle(vpiInitial, defn) reaches a sequential UDP's initial statement
// - the one that sets its starting state.
TEST_F(UdpModel, TraversesToInitial) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "seq_udp");
  VpiHandle init = MakeObject(vpiInitial, "init");
  defn->children.push_back(init);

  EXPECT_EQ(vpi_ctx_.Handle(vpiInitial, defn), init);
}

// C8: a table entry reports its number of symbol entries through vpiSize,
// handed back by the shared size dispatch.
TEST_F(UdpModel, TableEntrySizeReportsSymbolEntryCount) {
  VpiHandle row = MakeObject(vpiTableEntry, "row");
  row->size = 4;  // four symbols in this table row
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(row)), 4);
}

// C9 / Detail 1: a table entry's value is obtainable as a string (its
// decompiled symbol row). The read succeeds with no error.
TEST_F(UdpModel, TableEntryValueAllowsStringFormat) {
  auto* var = sim_ctx_.CreateVariable("te_str", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);  // 'A','B'
  VpiHandle row = MakeObject(vpiTableEntry, "row_str");
  row->var = var;

  s_vpi_value v = {};
  v.format = vpiStringVal;
  vpi_get_value(VpiHandleOf(row), &v);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_STREQ(v.value.str, "AB");
}

// C9 / Detail 1: a table entry's value is also obtainable as a vector (its
// symbols, two bytes each). The read succeeds with no error.
TEST_F(UdpModel, TableEntryValueAllowsVectorFormat) {
  auto* var = sim_ctx_.CreateVariable("te_vec", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);
  VpiHandle row = MakeObject(vpiTableEntry, "row_vec");
  row->var = var;

  s_vpi_value v = {};
  v.format = vpiVectorVal;
  vpi_get_value(VpiHandleOf(row), &v);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  ASSERT_NE(v.value.vector, nullptr);
  // §38.15: each symbol of the row "AB" takes two bytes, its character then
  // NUL.
  EXPECT_EQ(v.value.vector[0].aval, 0x41004200u);
}

// C9 / Detail 1 (the shall): no other format may be obtained for a table entry.
// A non-string, non-vector request is refused, records an error, and leaves the
// caller's value buffer untouched.
TEST_F(UdpModel, TableEntryValueRejectsOtherFormats) {
  auto* var = sim_ctx_.CreateVariable("te_int", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);
  VpiHandle row = MakeObject(vpiTableEntry, "row_int");
  row->var = var;

  s_vpi_value v = {};
  v.format = vpiIntVal;
  v.value.integer = 0x7777;  // sentinel that must survive the refused read
  vpi_get_value(VpiHandleOf(row), &v);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(v.value.integer, 0x7777);
}

// C9 / Detail 1 (the "only" boundary): the permitted set is exactly the
// decompilation string and the ASCII vector. Formats that are themselves string
// renderings - the binary/octal/hexadecimal radix strings - and the scalar/real
// numeric forms are still not among the two allowed forms, so the table-entry
// guard refuses each of them. This pins the boundary that a guard checking only
// for a string format alone would wrongly let through.
TEST_F(UdpModel, TableEntryValueRejectsStringLikeAndNumericFormats) {
  auto* var = sim_ctx_.CreateVariable("te_edge", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);
  VpiHandle row = MakeObject(vpiTableEntry, "row_edge");
  row->var = var;

  const int kRefused[] = {vpiBinStrVal, vpiOctStrVal, vpiHexStrVal,
                          vpiScalarVal, vpiRealVal};
  for (int format : kRefused) {
    s_vpi_value v = {};
    v.format = format;
    vpi_get_value(VpiHandleOf(row), &v);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "format " << format;
  }
}

// What the application found. A calltf is a plain C function with no return
// path to the case that provoked it.
int g_udp_defns = 0;
std::string g_udp_def_name;
int g_udp_inputs = 0;
int g_udp_prim_type = 0;
int g_udp_table_entries = 0;

PLI_INT32 ProbeUdpDefnsCalltf(PLI_BYTE8*) {
  // §37.4.3: the udp defn is drawn from a circle, so the iteration that reaches
  // the design's definitions is traversed with NULL for the ref_h.
  vpiHandle itr = vpi_iterate(vpiUdpDefn, nullptr);
  if (itr == nullptr) return 0;
  while (vpiHandle defn = vpi_scan(itr)) {
    ++g_udp_defns;
    if (const char* name = vpi_get_str(vpiDefName, defn)) {
      g_udp_def_name = name;
    }
    g_udp_inputs = vpi_get(vpiSize, defn);
    g_udp_prim_type = vpi_get(vpiPrimType, defn);
    if (vpiHandle rows = vpi_iterate(vpiTableEntry, defn)) {
      while (vpi_scan(rows) != nullptr) ++g_udp_table_entries;
    }
  }
  return 0;
}

// §37.36 against a design. Every property and relation the figure draws is
// drawn on a udp defn, and no pass built one, so the clause answered for no
// design at all: the circle iteration that is how an application reaches a
// design's UDP definitions returned none of them.
TEST(UdpDesign, ADesignsUdpDeclarationIsAUdpDefnObject) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_udp_defns = 0;
  g_udp_def_name.clear();
  g_udp_inputs = 0;
  g_udp_prim_type = 0;
  g_udp_table_entries = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeUdpDefnsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "primitive my_and(o, a, b);\n"
      "  output o;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 ? : 0;\n"
      "    ? 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module t;\n"
      "  wire o;\n"
      "  my_and u1(o, 1'b1, 1'b0);\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_udp_defns, 1);
  EXPECT_EQ(g_udp_def_name, "my_and");
  // The figure's "number of inputs" property.
  EXPECT_EQ(g_udp_inputs, 2);
  // Detail 2: a UDP with no state is combinational.
  EXPECT_EQ(g_udp_prim_type, vpiCombPrim);
  EXPECT_EQ(g_udp_table_entries, 3);
}

// §37.36: the UDP definitions of a design include the ones its UDP instances
// name, each once, however many instances name it and however deep they
// stand, here with no compilation unit to read the declarations of. A child
// instance with no module to stand for and a UDP instance naming no definition
// add none.
TEST(UdpDefinitionsOfADesign, EachDefinitionAnInstanceNamesOnce) {
  UdpDecl decl;
  decl.name = "u";
  RtlirModule leaf;
  leaf.udp_insts.resize(3);
  leaf.udp_insts[0].decl = &decl;
  leaf.udp_insts[1].decl = nullptr;
  leaf.udp_insts[2].decl = &decl;
  RtlirModule top;
  top.children.resize(2);
  top.children[0].resolved = &leaf;
  top.children[1].resolved = nullptr;
  RtlirDesign design;
  design.top_modules = {&top};

  EXPECT_EQ(VpiDesignUdpDecls(&design), (std::vector<const UdpDecl*>{&decl}));
}

// §37.36 against designs read and run whole, a udp defn read back once the run
// is over.
class UdpDefnsOfARun : public VpiDesignRun {
 protected:
  // §38.15: the symbols the vector value of the table entry `entry` holds,
  // `count` of them, each in two bytes of aval or bval, four to an element,
  // its second byte NUL for a one-character symbol.
  static std::vector<std::string> VectorSymbols(vpiHandle entry,
                                                std::size_t count) {
    s_vpi_value value = {};
    value.format = vpiVectorVal;
    vpi_get_value(entry, &value);
    std::vector<std::string> symbols;
    if (value.value.vector == nullptr) return symbols;
    for (std::size_t k = 0; k < count; ++k) {
      const s_vpi_vecval& element = value.value.vector[k / 4];
      const PLI_UINT32 kHalf = k % 4 < 2 ? element.aval : element.bval;
      const PLI_UINT32 kPair = (kHalf >> (k % 2 == 0 ? 16 : 0)) & 0xffffu;
      std::string symbol(1, static_cast<char>(kPair >> 8));
      if ((kPair & 0xffu) != 0) symbol.push_back(static_cast<char>(kPair));
      symbols.push_back(symbol);
    }
    return symbols;
  }

  // The string value of the table entry `entry`, empty for none.
  static std::string StringText(vpiHandle entry) {
    s_vpi_value value = {};
    value.format = vpiStringVal;
    vpi_get_value(entry, &value);
    return value.value.str == nullptr ? "" : value.value.str;
  }
};

// §37.36: the circle iteration reaches every UDP the design declares, one no
// instance uses among them, and a primitive written as an extern prototype and
// then defined once only (#7143).
TEST_F(UdpDefnsOfARun, EveryDeclaredUdpHasADefn) {
  Run("primitive used_and(o, a, b);\n"
      "  output o; input a, b;\n"
      "  table 0 ? : 0; ? 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "extern primitive spare_or(output o, input a, b);\n"
      "primitive spare_or(output o, input a, b);\n"
      "  table 1 ? : 1; ? 1 : 1; 0 0 : 0; endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire o;\n"
      "  used_and u1(o, 1'b1, 1'b0);\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiUdpDefn, nullptr),
            (std::vector<std::string>{"spare_or", "used_and"}));
}

constexpr const char* kFlop =
    "primitive flop(q, clk, d);\n"
    "  output reg q; input clk, d;\n"
    "  initial q = 1'b0;\n"
    "  table\n"
    "    r 0 : ? : 0;\n"
    "    (0x) 1 : 1 : 1;\n"
    "    ? * : ? : -;\n"
    "  endtable\n"
    "endprimitive\n"
    "primitive gate(o, a);\n"
    "  output o; input a;\n"
    "  table 0 : 1; 1 : 0; endtable\n"
    "endprimitive\n"
    "module top;\n"
    "  reg clk, d; wire q, o;\n"
    "  flop u1(q, clk, d);\n"
    "  gate u2(o, d);\n"
    "endmodule\n";

// §37.36 detail 1: a table entry's string value is its row as the table writes
// it, an edge in parentheses among its inputs and the current state of a
// sequential row in its own field, and its vector value holds its symbols, an
// edge's two characters together (#7141, #7461).
TEST_F(UdpDefnsOfARun, ATableEntryReadsAsItsRow) {
  Run(kFlop);
  const std::vector<vpiHandle> kRows =
      ObjectsOf(vpiTableEntry, Named(vpiUdpDefn, nullptr, "flop"));
  ASSERT_EQ(kRows.size(), 3u);
  EXPECT_EQ(StringText(kRows[0]), "r 0 : ? : 0");
  EXPECT_EQ(StringText(kRows[1]), "(0x) 1 : 1 : 1");
  EXPECT_EQ(StringText(kRows[2]), "? * : ? : -");
  EXPECT_EQ(VectorSymbols(kRows[1], 4),
            (std::vector<std::string>{"0x", "1", "1", "1"}));
  const std::vector<vpiHandle> kGateRows =
      ObjectsOf(vpiTableEntry, Named(vpiUdpDefn, nullptr, "gate"));
  ASSERT_EQ(kGateRows.size(), 2u);
  EXPECT_EQ(StringText(kGateRows[1]), "1 : 0");
}

// §37.36 (figure): a sequential UDP written with an initial statement reaches
// it from its defn, and a combinational one, written with none, reaches none
// (#7140).
TEST_F(UdpDefnsOfARun, ASequentialUdpReachesItsInitial) {
  Run(kFlop);
  vpiHandle flop = Named(vpiUdpDefn, nullptr, "flop");
  ASSERT_NE(flop, nullptr);
  vpiHandle initial = vpi_handle(vpiInitial, flop);
  ASSERT_NE(initial, nullptr);
  EXPECT_EQ(vpi_get(vpiType, initial), vpiInitial);
  EXPECT_EQ(vpi_handle(vpiInitial, Named(vpiUdpDefn, nullptr, "gate")),
            nullptr);
}

// §37.36 (figure) with §29.3.3 and §37.63: a UDP's initial runs a blocking
// assignment of the bit its output starts at to its output reg, x where the
// initial statement writes x (#7368).
TEST_F(UdpDefnsOfARun, AUdpsInitialAssignsItsOutput) {
  Run("primitive zero(q, d);\n"
      "  output reg q; input d;\n"
      "  initial q = 1'b0;\n"
      "  table 0 : ? : 0; 1 : ? : 1; endtable\n"
      "endprimitive\n"
      "primitive unknown(q, d);\n"
      "  output reg q; input d;\n"
      "  initial q = 1'bx;\n"
      "  table 0 : ? : 0; 1 : ? : 1; endtable\n"
      "endprimitive\n"
      "module top; reg d; wire a, b;\n"
      "  zero z(a, d); unknown u(b, d);\n"
      "endmodule\n");
  vpiHandle zero = vpi_handle(
      vpiStmt, vpi_handle(vpiInitial, Named(vpiUdpDefn, nullptr, "zero")));
  ASSERT_NE(zero, nullptr);
  EXPECT_EQ(vpi_get(vpiType, zero), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiBlocking, zero), 1);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, zero)), "q");
  s_vpi_value value = {};
  value.format = vpiBinStrVal;
  vpi_get_value(vpi_handle(vpiRhs, zero), &value);
  EXPECT_STREQ(value.value.str, "0");
  vpiHandle unknown = vpi_handle(
      vpiStmt, vpi_handle(vpiInitial, Named(vpiUdpDefn, nullptr, "unknown")));
  ASSERT_NE(unknown, nullptr);
  vpi_get_value(vpi_handle(vpiRhs, unknown), &value);
  EXPECT_STREQ(value.value.str, "x");
}

constexpr std::string_view kUdpKey = "udp-exchange-key";

// §37.36 with §37.3.6: a UDP declared in a decryption envelope is protected
// code, and one written in the clear answers vpiProtected FALSE, without error
// (#7142).
TEST_F(UdpDefnsOfARun, ASealedUdpIsProtected) {
  RunUnderKey(EncryptEnvelopes("`pragma protect begin\n"
                               "primitive sealed_and(o, a, b);\n"
                               "  output o; input a, b;\n"
                               "  table 0 ? : 0; ? 0 : 0; 1 1 : 1; endtable\n"
                               "endprimitive\n"
                               "`pragma protect end\n"
                               "primitive clear_not(o, a);\n"
                               "  output o; input a;\n"
                               "  table 0 : 1; 1 : 0; endtable\n"
                               "endprimitive\n"
                               "module t;\n"
                               "  wire o1, o2;\n"
                               "  sealed_and u1(o1, 1'b1, 1'b0);\n"
                               "  clear_not u2(o2, 1'b1);\n"
                               "endmodule\n",
                               kUdpKey),
              kUdpKey, f_);
  std::vector<int> sealed;
  vpiHandle clear = nullptr;
  for (vpiHandle defn : ObjectsOf(vpiUdpDefn, nullptr)) {
    sealed.push_back(vpi_get(vpiIsProtected, defn));
    if (sealed.back() == 0) clear = defn;
  }
  std::ranges::sort(sealed);
  EXPECT_EQ(sealed, (std::vector<int>{0, 1}));
  ASSERT_NE(clear, nullptr);
  EXPECT_EQ(vpi_get(vpiProtected, clear), 0);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.15: the vector value of a table entry is its symbols, two bytes each,
// the first two in aval's halves and the third in bval's upper half (#7461).
TEST_F(UdpDefnsOfARun, ATableEntrysVectorHoldsTwoBytesPerSymbol) {
  Run("primitive p(output o, input a, b);\n"
      "  table\n"
      "    1 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire o, a, b;\n"
      "  p g(o, a, b);\n"
      "  initial $noop;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kRows =
      ObjectsOf(vpiTableEntry, Named(vpiUdpDefn, nullptr, "p"));
  ASSERT_EQ(kRows.size(), 1u);
  s_vpi_value value = {};
  value.format = vpiVectorVal;
  vpi_get_value(kRows[0], &value);
  ASSERT_NE(value.value.vector, nullptr);
  EXPECT_EQ(value.value.vector[0].aval, 0x31003000u);
  EXPECT_EQ(value.value.vector[0].bval, 0x31000000u);
}

}  // namespace
}  // namespace delta
