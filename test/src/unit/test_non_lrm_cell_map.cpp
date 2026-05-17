#include <gtest/gtest.h>

#include <string>

#include "synthesizer/aig.h"
#include "synthesizer/cell_map.h"
#include "synthesizer/liberty.h"

using namespace delta;

Liberty MakeTestLib() {
  Liberty lib;
  lib.library_name = "testlib";

  {
    LibCell cell;
    cell.name = "INV";
    cell.area = 1.0f;
    cell.pins.push_back({"A", "input", ""});
    cell.pins.push_back({"Y", "output", "!A"});
    lib.cells.push_back(std::move(cell));
  }

  {
    LibCell cell;
    cell.name = "AND2";
    cell.area = 2.0f;
    cell.pins.push_back({"A", "input", ""});
    cell.pins.push_back({"B", "input", ""});
    cell.pins.push_back({"Y", "output", "A * B"});
    lib.cells.push_back(std::move(cell));
  }

  {
    LibCell cell;
    cell.name = "OR2";
    cell.area = 2.0f;
    cell.pins.push_back({"A", "input", ""});
    cell.pins.push_back({"B", "input", ""});
    cell.pins.push_back({"Y", "output", "A + B"});
    lib.cells.push_back(std::move(cell));
  }

  return lib;
}

namespace {

TEST(CellMap, SingleAndGate) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  auto lib = MakeTestLib();
  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.instances.size(), 1);
  EXPECT_EQ(mapping.instances[0].cell_name, "AND2");
  EXPECT_EQ(mapping.instances[0].input_nets.size(), 2);
}

TEST(CellMap, InverterGate) {
  AigGraph g;
  auto a = g.AddInput();
  auto not_a = g.AddNot(a);
  g.AddOutput(not_a);

  auto lib = MakeTestLib();
  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.instances.size(), 1);
  EXPECT_EQ(mapping.instances[0].cell_name, "INV");
  EXPECT_EQ(mapping.instances[0].input_nets.size(), 1);
}

TEST(CellMap, OrGateMapping) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddOr(a, b);
  g.AddOutput(c);

  auto lib = MakeTestLib();
  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.instances.size(), 1);
  EXPECT_EQ(mapping.instances[0].cell_name, "OR2");
  EXPECT_EQ(mapping.instances[0].input_nets.size(), 2);
}

TEST(CellMap, NoMatchingCell) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddXor(a, b);
  g.AddOutput(c);

  auto lib = MakeTestLib();

  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  EXPECT_GE(mapping.instances.size(), 1);
}

TEST(CellMap, MultiOutputDesign) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto and_ab = g.AddAnd(a, b);
  auto not_a = g.AddNot(a);
  g.AddOutput(and_ab);
  g.AddOutput(not_a);

  auto lib = MakeTestLib();
  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  ASSERT_EQ(mapping.instances.size(), 2);
  EXPECT_EQ(mapping.instances[0].cell_name, "AND2");
  EXPECT_EQ(mapping.instances[1].cell_name, "INV");
}

}
