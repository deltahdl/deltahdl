#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "gtest/gtest.h"
#include "simulator/statement_assign.h"

using namespace delta;

// Assigns the given right-hand-side expression to queue "q", runs the queue
// blocking-assignment collector, and returns the resulting queue object.
inline QueueObject* AssignRhsToQueueQ(Expr* rhs, SimFixture& f) {
  auto* stmt = MakeAssign(f.arena, "q", rhs);
  TryQueueBlockingAssign(stmt, f.ctx, f.arena);
  return f.ctx.FindQueue("q");
}

// Asserts that the named queue exists and holds exactly the expected element
// values (compared as unsigned 64-bit integers).
inline void ExpectQueueContents(SimFixture& f, std::string_view name,
                                const std::vector<uint64_t>& expected) {
  auto* q = f.ctx.FindQueue(name);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    EXPECT_EQ(q->elements[i].ToUint64(), expected[i]);
  }
}
