#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.36 "UDP": the VPI object model for a UDP definition (the "udp defn" node),
// its io decl, table entry, and initial children, and the table entry's own
// size and value. The udp instance and the udp -> udp defn edge belong to the
// neighboring §37.35 (Primitive, prim term); this clause owns the udp defn's
// properties and the two numbered Details.
//
//   defn vpiDefName  - the definition name a udp defn reports (string dispatch).
//   defn vpiSize     - the number of inputs (the shared kVpiSize dispatch).
//   defn vpiProtected- the protection flag every object carries (§37.3.6).
//   defn vpiPrimType - the primitive type; Detail 2 fixes vpiSeqPrim for a
//                      sequential UDP and vpiCombPrim for a combinational one.
//   defn -> io decl / table entry / initial - one-to-many/one-to-one traversals
//                      served by the generic child walk.
//   table entry vpiSize - the number of symbol entries (shared size dispatch).
//   table entry value   - Detail 1 allows only a string (decompilation) and a
//                      vector (ASCII symbol values) through vpi_get_value().
//
// The fixture installs a context so the public vpi_* entry points run their real
// dispatch, and provides the simulation plumbing a table-entry value read needs.
class UdpModel : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // A bare context-owned object of the requested kind, stamped with the name the
  // test wants - the same approach the §37.37 model tests use.
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
  EXPECT_STREQ(vpi_get_str(vpiDefName, defn), "latch_udp");
}

// C2: a udp defn reports its number of inputs through vpiSize, which the shared
// size dispatch hands back from the stored size.
TEST_F(UdpModel, SizeReportsNumberOfInputs) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "mux_udp");
  defn->size = 3;  // a three-input UDP
  EXPECT_EQ(vpi_get(vpiSize, defn), 3);
}

// C3: a udp defn carries the vpiProtected Boolean (§37.3.6), TRUE when it stands
// for protected code and FALSE otherwise. §37.3.6 lets this property through even
// for a protected object.
TEST_F(UdpModel, ProtectedFlagReported) {
  VpiHandle open_defn = MakeObject(vpiUdpDefn, "open_udp");
  EXPECT_EQ(vpi_get(vpiIsProtected, open_defn), 0);

  VpiHandle sealed_defn = MakeObject(vpiUdpDefn, "sealed_udp");
  sealed_defn->is_protected = true;
  EXPECT_EQ(vpi_get(vpiIsProtected, sealed_defn), 1);
}

// C4 / Detail 2: a sequential UDP reports vpiSeqPrim through vpiPrimType.
TEST_F(UdpModel, PrimTypeReportsSequentialUdp) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "ff_udp");
  defn->prim_type = vpiSeqPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, defn), vpiSeqPrim);
}

// C4 / Detail 2: a combinational UDP reports vpiCombPrim through vpiPrimType.
TEST_F(UdpModel, PrimTypeReportsCombinationalUdp) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "and_udp");
  defn->prim_type = vpiCombPrim;
  EXPECT_EQ(vpi_get(vpiPrimType, defn), vpiCombPrim);
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

  vpiHandle iter = vpi_iterate(vpiIODecl, defn);
  ASSERT_NE(iter, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle d = vpi_scan(iter)) seen.push_back(d);
  ASSERT_EQ(static_cast<int>(seen.size()), 3);
  EXPECT_EQ(seen[0], out);
  EXPECT_EQ(seen[1], in0);
  EXPECT_EQ(seen[2], in1);
}

// C6: iterating vpiTableEntry from a udp defn walks the rows of its state table.
TEST_F(UdpModel, TraversesToTableEntries) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "tab_udp");
  VpiHandle row0 = MakeObject(vpiTableEntry, "r0");
  VpiHandle row1 = MakeObject(vpiTableEntry, "r1");
  defn->children.push_back(row0);
  defn->children.push_back(row1);

  vpiHandle iter = vpi_iterate(vpiTableEntry, defn);
  ASSERT_NE(iter, nullptr);
  std::vector<vpiHandle> seen;
  while (vpiHandle r = vpi_scan(iter)) seen.push_back(r);
  ASSERT_EQ(static_cast<int>(seen.size()), 2);
  EXPECT_EQ(seen[0], row0);
  EXPECT_EQ(seen[1], row1);
}

// C7: vpi_handle(vpiInitial, defn) reaches a sequential UDP's initial statement -
// the one that sets its starting state.
TEST_F(UdpModel, TraversesToInitial) {
  VpiHandle defn = MakeObject(vpiUdpDefn, "seq_udp");
  VpiHandle init = MakeObject(vpiInitial, "init");
  defn->children.push_back(init);

  EXPECT_EQ(vpi_ctx_.Handle(vpiInitial, defn), init);
}

// C8: a table entry reports its number of symbol entries through vpiSize, handed
// back by the shared size dispatch.
TEST_F(UdpModel, TableEntrySizeReportsSymbolEntryCount) {
  VpiHandle row = MakeObject(vpiTableEntry, "row");
  row->size = 4;  // four symbols in this table row
  EXPECT_EQ(vpi_get(vpiSize, row), 4);
}

// C9 / Detail 1: a table entry's value is obtainable as a string (its decompiled
// symbol row). The read succeeds with no error.
TEST_F(UdpModel, TableEntryValueAllowsStringFormat) {
  auto* var = sim_ctx_.CreateVariable("te_str", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);  // 'A','B'
  VpiHandle row = MakeObject(vpiTableEntry, "row_str");
  row->var = var;

  s_vpi_value v = {};
  v.format = vpiStringVal;
  vpi_get_value(row, &v);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
  EXPECT_STREQ(v.value.str, "AB");
}

// C9 / Detail 1: a table entry's value is also obtainable as a vector (its ASCII
// symbol values). The read succeeds with no error.
TEST_F(UdpModel, TableEntryValueAllowsVectorFormat) {
  auto* var = sim_ctx_.CreateVariable("te_vec", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);
  VpiHandle row = MakeObject(vpiTableEntry, "row_vec");
  row->var = var;

  s_vpi_value v = {};
  v.format = vpiVectorVal;
  vpi_get_value(row, &v);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
  ASSERT_NE(v.value.vector, nullptr);
  EXPECT_EQ(v.value.vector[0].aval, 0x4142u);
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
  vpi_get_value(row, &v);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(v.value.integer, 0x7777);
}

// C9 / Detail 1 (the "only" boundary): the permitted set is exactly the
// decompilation string and the ASCII vector. Formats that are themselves string
// renderings - the binary/octal/hexadecimal radix strings - and the scalar/real
// numeric forms are still not among the two allowed forms, so the table-entry
// guard refuses each of them. This pins the boundary that a guard checking only
// for "a string format" would wrongly let through.
TEST_F(UdpModel, TableEntryValueRejectsStringLikeAndNumericFormats) {
  auto* var = sim_ctx_.CreateVariable("te_edge", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x4142);
  VpiHandle row = MakeObject(vpiTableEntry, "row_edge");
  row->var = var;

  const int refused[] = {vpiBinStrVal, vpiOctStrVal, vpiHexStrVal, vpiScalarVal,
                         vpiRealVal};
  for (int format : refused) {
    s_vpi_value v = {};
    v.format = format;
    vpi_get_value(row, &v);

    SVpiErrorInfo info = {};
    EXPECT_EQ(VpiChkErrorC(&info), vpiError) << "format " << format;
  }
}

}  // namespace
}  // namespace delta
