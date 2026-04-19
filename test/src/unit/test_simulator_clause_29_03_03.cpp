#include <gtest/gtest.h>

#include "parser/ast.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

UdpDecl MakeSequentialUdpWithInitial(char init) {
  UdpDecl decl;
  decl.is_sequential = true;
  decl.has_initial = true;
  decl.initial_value = init;
  return decl;
}

TEST(UdpInitialStatement, OutputIsZeroAtSimulationStart) {
  auto decl = MakeSequentialUdpWithInitial('0');
  UdpEvalState state(decl);
  EXPECT_EQ(state.GetOutput(), '0');
}

TEST(UdpInitialStatement, OutputIsOneAtSimulationStart) {
  auto decl = MakeSequentialUdpWithInitial('1');
  UdpEvalState state(decl);
  EXPECT_EQ(state.GetOutput(), '1');
}

TEST(UdpInitialStatement, OutputIsXAtSimulationStart) {
  auto decl = MakeSequentialUdpWithInitial('x');
  UdpEvalState state(decl);
  EXPECT_EQ(state.GetOutput(), 'x');
}

}  // namespace
