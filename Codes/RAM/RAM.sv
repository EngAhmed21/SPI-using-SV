module RAM(slave_RAM_intf.RAM SR_intf);
	localparam MEM_DEPTH = SR_intf.MEM_DEPTH;
	localparam ADDR_SIZE = $clog2(MEM_DEPTH);

	logic clk, rst_n, rx_valid, tx_valid;
	logic [ADDR_SIZE + 1 : 0] din;
    logic [ADDR_SIZE - 1 : 0] dout;

	assign clk 					= SR_intf.clk;
	assign rst_n 				= SR_intf.rst_n;
	assign rx_valid 			= SR_intf.rx_valid;
	assign din 					= SR_intf.rx_data;
	assign SR_intf.tx_data 		= dout;
	assign SR_intf.tx_valid 	= tx_valid;

	logic [ADDR_SIZE - 1 : 0] mem [MEM_DEPTH - 1 : 0];
	logic [ADDR_SIZE - 1 : 0] wr_addr, rd_addr;

	always @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			dout 	 <= 0;
			wr_addr  <= 0;
			rd_addr  <= 0;
		end
		else if (rx_valid)
			case (din [ADDR_SIZE + 1 : ADDR_SIZE])
				2'b00:	wr_addr 	  <= din [ADDR_SIZE - 1 : 0];						
				2'b01:	mem [wr_addr] <= din [ADDR_SIZE - 1 : 0];
				2'b10:	rd_addr 	  <= din [ADDR_SIZE - 1 : 0];
				2'b11:  dout 		  <= mem [rd_addr];
			endcase
	end

	always @(posedge clk, negedge rst_n) begin
		if (!rst_n)
			tx_valid <= 0;
		else if (rx_valid)
			if (&(din [ADDR_SIZE + 1 : ADDR_SIZE]))
				tx_valid <= 1;
			else
				tx_valid <= 0;
	end

	// Assertions for the internal signals
	`ifdef SIM
		// Check reset values
		always_comb begin
			if (!rst_n) begin
				rst_wr_addr_a:	assert final (wr_addr == 0);
				rst_rd_addr_a:	assert final (rd_addr == 0);
			end
		end

		// wr_addr
		property wr_addr_pr;
			@(posedge clk) disable iff(!rst_n) (((rx_valid) && (din [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b00))) |=> 
			 (wr_addr == $past(din [ADDR_SIZE - 1 : 0]));
		endproperty
		wr_addr_a:	  assert property (wr_addr_pr);
		wr_addr_cov:  cover  property (wr_addr_pr);

		// rd_addr
		property rd_addr_pr;
			@(posedge clk) disable iff(!rst_n) (((rx_valid) && (din [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b10))) |=> 
			 (rd_addr == $past(din [ADDR_SIZE - 1 : 0]));
		endproperty
		rd_addr_a:	  assert property (rd_addr_pr);
		rd_addr_cov:  cover  property (rd_addr_pr);

		// mem
		property mem_pr;
			@(posedge clk) disable iff(!rst_n) (((rx_valid) && (din [ADDR_SIZE + 1 : ADDR_SIZE] == 2'b01))) |=>
			 (mem [wr_addr] == $past(din [ADDR_SIZE - 1 : 0]));
		endproperty
		mem_a:	  assert property (mem_pr);
		mem_cov:  cover  property (mem_pr);
	`endif 
endmodule