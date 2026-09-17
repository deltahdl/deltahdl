// IEEE 1800-2023 §18.17.3: a case production statement evaluates its case
// expression and compares it against each case item expression in the order
// given, generating the production of the first matching item, the default
// item's production when none matches, or nothing when there is no default;
// case item expressions separated by commas share a production. The clause's
// SELECT compares device & 7 against 0 for NETWORK and 1, 2 for DISK with
// MEMORY as default, so a device of 8 selects network, 9 and 10 disk, 11
// memory and 16 network again; the first of two matching items wins; and a
// case with no match and no default generates nothing.
module case_production;
  int device, i, first_wins, nothing;
  int devices[5];

  initial begin
    devices[0] = 8; devices[1] = 9; devices[2] = 10; devices[3] = 11; devices[4] = 16;
    for (i = 0; i < 5; i++) begin
      device = devices[i];
      $write("device %0d selects ", device);
      randsequence()
        SELECT : case ( device & 7 )
          0       : NETWORK ;
          1, 2    : DISK ;
          default : MEMORY ;
        endcase ;
        NETWORK : { $display("network"); } ;
        DISK    : { $display("disk"); } ;
        MEMORY  : { $display("memory"); } ;
      endsequence
    end

    first_wins = 0;
    randsequence()
      PICK : case ( 1 )
        1 : A ;
        1 : B ;
      endcase ;
      A : { first_wins = 1; } ;
      B : { first_wins = 2; } ;
    endsequence
    nothing = 1;
    randsequence()
      PICK : case ( 5 )
        1 : A ;
        2 : A ;
      endcase ;
      A : { nothing = 0; } ;
    endsequence
    first_wins = first_wins == 1;
    $display("the first of two matching items wins: %0d, no match and no default generates nothing: %0d",
             first_wins, nothing);
    $finish;
  end
endmodule
