#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.35 Primitive, prim term: the VPI object model for a primitive (gate,
// switch, or UDP) and the prim-term objects that carry its terminals. The
// diagram's property labels (vpiDefName, vpiName/vpiFullName, vpiPrimType,
// vpiStrength0/1, the array-member booleans) and structural edges (to module,
// primitive array, udp defn, the delay expr, and the prim term's value/direction)
// are read by the generic object-model machinery and the value/delay routines
// owned by other subclauses. The four numbered Details carry this clause's own
// rules, and the tests below observe the production code that applies them:
//   D1 - vpiSize returns a primitive's number of inputs (the kVpiSize dispatch).
//   D2 - vpi_put_value() is allowed only on a sequential UDP primitive
//        (the guard at the head of PutValue).
//   D3 - vpiTermIndex reports a prim term's terminal order, first index zero
//        (the vpiTermIndex dispatch).
//   D4 - vpiIndex from a primitive reaches its array index, or NULL when the
//        primitive is not an array element (the Handle transition).

// The fixture installs a context so the public vpi_get/vpi_handle/vpi_put_value
// entry points run their real dispatch, and provides the simulation plumbing a
// sequential-UDP value put needs.
class PrimitivePrimTerm : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// D1: vpiSize on a primitive reports its number of inputs. A primitive stores
// that input count as its size, and vpi_get(vpiSize) hands it back through the
// shared size dispatch.
TEST_F(PrimitivePrimTerm, SizeReportsNumberOfInputs) {
  VpiObject prim;
  prim.type = vpiPrimitive;
  prim.size = 3;  // a three-input primitive
  EXPECT_EQ(vpi_get(vpiSize, &prim), 3);

  VpiObject gate;
  gate.type = vpiGate;
  gate.size = 2;
  EXPECT_EQ(vpi_get(vpiSize, &gate), 2);
}

// D3: a prim term reports its terminal index through vpiTermIndex, which fixes
// the terminal order. The first terminal carries index zero; successive
// terminals report 1, 2, ... so the order is recoverable.
TEST_F(PrimitivePrimTerm, TermIndexReportsTerminalOrder) {
  VpiObject first;
  first.type = vpiPrimTerm;
  first.index = 0;
  VpiObject second;
  second.type = vpiPrimTerm;
  second.index = 1;
  VpiObject third;
  third.type = vpiPrimTerm;
  third.index = 2;

  // The first terminal has term index zero.
  EXPECT_EQ(vpi_get(vpiTermIndex, &first), 0);
  EXPECT_EQ(vpi_get(vpiTermIndex, &second), 1);
  EXPECT_EQ(vpi_get(vpiTermIndex, &third), 2);
}

// D4: vpiIndex from a primitive that is an element of a primitive array reaches
// the index expression that locates it within the array.
TEST_F(PrimitivePrimTerm, IndexTransitionReachesArrayIndex) {
  VpiObject index_expr;
  index_expr.type = vpiConstant;

  VpiObject member;
  member.type = vpiPrimitive;
  member.array_member = true;
  member.index_expr = &index_expr;

  EXPECT_EQ(VpiHandleC(vpiIndex, &member), &index_expr);
}

// D4: for a primitive that is not part of a primitive array, the vpiIndex
// transition returns NULL - even if some other expr is hanging off the object,
// the transition is meaningful only for an array member.
TEST_F(PrimitivePrimTerm, IndexTransitionIsNullWhenNotAnArrayElement) {
  VpiObject stray_expr;
  stray_expr.type = vpiConstant;

  VpiObject standalone;
  standalone.type = vpiPrimitive;
  standalone.array_member = false;
  standalone.index_expr = &stray_expr;  // present but must not be reported
  standalone.children.push_back(&stray_expr);

  EXPECT_EQ(VpiHandleC(vpiIndex, &standalone), nullptr);
}

// D2: vpi_put_value() applied to a primitive that is not a sequential UDP - a
// gate, switch, combinational UDP, or generic primitive - is rejected. The put
// returns NULL and records a vpi_chk_error() error, leaving nothing written.
TEST_F(PrimitivePrimTerm, PutValueRejectedOnNonSequentialPrimitive) {
  const int kinds[] = {vpiGate, vpiSwitch, vpiUdp, vpiCombPrim, vpiPrimitive};
  for (int kind : kinds) {
    VpiObject prim;
    prim.type = kind;

    s_vpi_value val = {};
    val.format = vpiScalarVal;
    val.value.scalar = vpi1;
    vpiHandle ret = vpi_put_value(&prim, &val, nullptr, vpiNoDelay);
    EXPECT_EQ(ret, nullptr) << "kind " << kind;

    SVpiErrorInfo info = {};
    EXPECT_EQ(VpiChkErrorC(&info), vpiError) << "kind " << kind;
  }
}

// D2: the same routine accepts a value put to a sequential UDP - the one
// primitive kind that may be written. The §37.35 restriction does not fire, and
// (with the required vpiNoDelay flag) the value is applied with no error.
TEST_F(PrimitivePrimTerm, PutValueAcceptedOnSequentialUdp) {
  auto* var = sim_ctx_.CreateVariable("seq", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("seq", nullptr);
  ASSERT_NE(h, nullptr);
  h->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

}  // namespace
}  // namespace delta
