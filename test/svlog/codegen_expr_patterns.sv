module A #(
	parameter type tag_t = logic [4:0]
)(
	input  tag_t          lsu_qtag_i,
	input  logic          lsu_qsigned,
	input  logic [31:0]   lsu_qaddr_i,
	input  logic [1:0]    lsu_qsize_i
);
	typedef struct packed {
		tag_t       tag;
		logic       sign_ext;
		logic [2:0] offset;
		logic [1:0] size;
	} laq_t;

	laq_t laq_in;

	assign laq_in = '{
		tag:      lsu_qtag_i,
		sign_ext: lsu_qsigned,
		offset:   lsu_qaddr_i[2:0],
		size:     lsu_qsize_i
	};
endmodule
