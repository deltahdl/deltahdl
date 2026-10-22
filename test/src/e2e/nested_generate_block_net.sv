// IEEE 1800-2023 §23.9: an identifier a task, function, named block or
// generate block names without a hierarchical path has to be declared either
// in that scope itself or in a module, interface, program, checker, task,
// function, named block or generate block above it on the same branch of the
// name tree, and the lookup climbs outward until it finds the name or reaches
// the boundary of a module, interface, program or checker. Block b is higher in
// the same branch than block a, so the w that a writes is the w that b
// declared.
//
// §27.4 has each of them, once instantiated, open a scope of its own and a
// further level of hierarchy, so a lookup that tries only the innermost block
// and then the module skips b entirely. Where the reference is on the left of a
// continuous assignment or in a terminal list, §6.10 then assumes an implicit
// net for it, and the source drives a second w that nothing reads.
//
// The write and the read stand in different blocks and at different times: a
// writes at time 0 and b reads at time 1, so the value printed is one that
// crossed the block boundary rather than one either block could have produced
// alone.
module nested_generate_block_net;
  generate
    if (1) begin : b
      logic w;

      if (1) begin : a
        initial w = 1'b1;
      end

      initial begin
        #1;
        $display("%0d", w);
      end
    end
  endgenerate
endmodule
