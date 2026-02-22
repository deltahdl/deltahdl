// Non-LRM tests

#include "synthesis/aig.h"
#include "synthesis/cell_map.h"
#include "synthesis/liberty.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Helper: build a minimal Liberty library for testing
// =============================================================================
Liberty MakeTestLib() {
  Liberty lib;
  lib.library_name = "testlib";

  // INV cell: Y = !A
  {
    LibCell cell;
    cell.name = "INV";
    cell.area = 1.0f;
    cell.pins.push_back({"A", "input", ""});
    cell.pins.push_back({"Y", "output", "!A"});
    lib.cells.push_back(std::move(cell));
  }

  // AND2 cell: Y = A * B
  {
    LibCell cell;
    cell.name = "AND2";
    cell.area = 2.0f;
    cell.pins.push_back({"A", "input", ""});
    cell.pins.push_back({"B", "input", ""});
    cell.pins.push_back({"Y", "output", "A * B"});
    lib.cells.push_back(std::move(cell));
  }

  // OR2 cell: Y = A + B
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

// =============================================================================
// Map single AND gate to AND2 cell
// =============================================================================
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

// =============================================================================
// Map inverter to INV cell
// =============================================================================
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

// =============================================================================
// Map OR gate (using De Morgan) to OR2 cell
// =============================================================================
TEST(CellMap, OrGateMapping) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddOr(a, b);
  g.AddOutput(c);

  auto lib = MakeTestLib();
  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  // OR via De Morgan is ~(~a & ~b). The mapper should recognize the OR
  // pattern and produce an OR2 cell.
  ASSERT_EQ(mapping.instances.size(), 1);
  EXPECT_EQ(mapping.instances[0].cell_name, "OR2");
  EXPECT_EQ(mapping.instances[0].input_nets.size(), 2);
}

// =============================================================================
// Handle no matching cell
// =============================================================================
TEST(CellMap, NoMatchingCell) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddXor(a, b);
  g.AddOutput(c);

  // Library with only INV and AND2 (no XOR).
  Liberty lib;
  lib.library_name = "limited";
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

  CellMapper mapper(lib);
  auto mapping = mapper.Map(g);

  // XOR cannot be mapped to a single cell in this library, so the mapper
  // decomposes it. We just verify it produces some output.
  EXPECT_GE(mapping.instances.size(), 1);
}

// =============================================================================
// Map multi-output design
// =============================================================================
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

} // namespace
