#pragma once

#include <vector>

#include "parser/ast.h"

using namespace delta;

struct UdpBuilder {
  UdpDecl decl;

  UdpBuilder& SetSequential() {
    decl.is_sequential = true;
    return *this;
  }

  UdpBuilder& SetInitial(char val) {
    decl.has_initial = true;
    decl.initial_value = val;
    return *this;
  }

  UdpBuilder& AddSeqRow(std::vector<char> inputs, char state, char output) {
    UdpTableRow row;
    row.inputs = std::move(inputs);
    row.current_state = state;
    row.output = output;
    decl.table.push_back(row);
    return *this;
  }
};
