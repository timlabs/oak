require_relative 'parser.rb'
require_relative 'proof_methods.rb'
require_relative 'utilities.rb'

class Proof
	def self.process input, is_filename = false
		proof = Proof.new
		include proof, input, is_filename

		message = case proof.scopes.last
			when :suppose then 'error at end of input: active supposition'
			when :now then 'error at end of input: active "now" block'
			when Array then 'error at end of input: active "proof" block'
			when :assume then 'error at end of input: active assume block'
		end
		if message
			puts message
			raise ProofException, message
		end

		puts "all lines accepted"

		if proof.makes_assumptions?
			proof.print_assumptions
			puts 'proof incomplete due to assumptions'
		else
			proof.print_axioms
			puts 'proof successful!'
		end
	end

	def self.include proof, input, is_path = false
		if is_path
			dirname = File.dirname input
			filename = File.basename input
			begin
				input = File.read input
			rescue
				puts "error: could not open file \"#{input}\""
				raise ProofException
			end
		else
			filename = ''
		end
		begin
			wrapper = WordWrapper.new ' ', 2
			line_number = nil # external scope, for error reporting
			from_include = false
			wrapper.print "#{filename}: processing line "
			Parser.new.parse_each(input) {|sentence, action, content, reasons, label, fileline|
				next if action == :empty
				break if action == :exit
				line_number = fileline
				wrapper.print "#{line_number} "
				content = process_content content, proof.theses[-1] if content.is_a? Tree
				id = {:label => label, :filename => filename, :fileline => fileline}
				case action
					when :include then
						# include relative to path of current proof file
						content = File.expand_path content, dirname if is_path
						wrapper.puts
						from_include = true
						include proof, content, :is_filename
						from_include = false
						wrapper.print "#{filename}: processing line "
					when :suppose then proof.suppose content, id
					when :now then proof.now
					when :end then proof.end_block
					when :assume then proof.assume content, id
					when :assume_schema then proof.assume_schema content, id
					when :axiom then proof.axiom content, id
					when :axiom_schema then proof.axiom_schema content, id
					when :derive then proof.derive content, reasons, id
					when :so then proof.so content, reasons, id
					when :so_assume then proof.so_assume content, id
					when :proof then proof.proof content, id
					when :begin_assume then proof.begin_assume id
					when :end_assume then proof.end_assume
					else raise "unrecognized action #{action}"
				end
			}
		rescue ProofException => e
			message = case e
				when ParseException then e.message
				when DeriveException then e.message line_number
				else "error at line #{line_number}: #{e}"
			end
			if not from_include # already printed otherwise
				wrapper.puts e.line_number if e.is_a? ParseException
				wrapper.puts if not e.is_a? ParseException
				wrapper.puts message
			end
			raise e, message # preserve exception class
		end
		puts
	end

	private_class_method def self.process_content tree, thesis
		if thesis
			begin
				substitute tree, {'thesis' => thesis}
			rescue SubstituteException => e
				raise ProofException, "cannot bind variable #{e}: part of thesis"
			end
		elsif tree.free_variables.include? 'thesis'
			raise ProofException, 'thesis used outside of proof block'
		else
			tree
		end
	end
end