import RAM_pkg::*;

module RAM_tb (slave_RAM_intf.RAM_test SR_intf);
	localparam MEM_DEPTH = SR_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	logic clk, rst_n, rx_valid, tx_valid;
	logic [ADDR_SIZE + 1 : 0] rx_data;
	logic [ADDR_SIZE - 1 : 0] tx_data;

	logic tx_valid_ref;
	logic [ADDR_SIZE - 1 : 0] tx_data_ref, wr_addr, rd_addr;
	logic [ADDR_SIZE - 1 : 0] mem_test [MEM_DEPTH];

	RAM_tr #(.MEM_DEPTH(MEM_DEPTH)) tr;

	assign clk 					= SR_intf.clk;
	assign SR_intf.rst_n 		= rst_n;
	assign SR_intf.rx_valid 	= rx_valid;
	assign SR_intf.rx_data      = rx_data;
	assign tx_data              = SR_intf.tx_data;
	assign tx_valid             = SR_intf.tx_valid;

	always @(posedge clk) 
        tr.cvgrp.sample();

    initial begin
		tr = new();
		rst_n = 0;

		@(negedge clk);
		repeat (10000) begin
			RAM_ra:	assert (tr.randomize());
			rst_n 		= tr.rst_n;
			rx_valid 	= tr.rx_valid;
			rx_data     = tr.rx_data;
			@(negedge clk);
		end
		$stop;
    end
endmodule