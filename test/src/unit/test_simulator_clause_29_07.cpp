// §29.7: Sequential UDP initialization

#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulation/udp_eval.h"

using namespace delta;

namespace {

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder &SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder &SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }
};

TEST(UdpInit, DefaultIsX) {
  UdpBuilder b;
  b.SetSequential();

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), 'x');
}

TEST(UdpInit, InitialValueOne) {
  UdpBuilder b;
  b.SetSequential().SetInitial('1');

  UdpEvalState state(b.decl);
  EXPECT_EQ(state.GetOutput(), '1');
}

} // namespace
