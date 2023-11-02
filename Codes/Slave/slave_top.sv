module slave_top ();
    bit clk;
    localparam MEM_DEPTH = 256;

    logic SS_n, MOSI, MISO;

    slave_RAM_intf #(.MEM_DEPTH(MEM_DEPTH)) SR_intf(clk);

    slave DUT (SS_n, MOSI, SR_intf, MISO);

    slave_tb TEST (MISO, SR_intf, SS_n, MOSI);

     initial begin
        clk = 1;
        forever 
            #1 clk = ~clk;
    end
endmodule