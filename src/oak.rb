if RUBY_VERSION < '2'
	puts "Oak requires Ruby version >= 2.0.  (You have Ruby #{RUBY_VERSION}.)"
	exit
end

require_relative 'proof.rb'

name_version = 'Oak version 0.5'
issues_url = 'https://github.com/timlabs/oak/issues'

options = {}

if ARGV.delete '-v'
	puts name_version
	exit if ARGV.size == 0
end

if ARGV.delete '-c'
	options[:reduce] = true
end

if ARGV.delete '-w'
	options[:wait] = true
end

if ARGV.size != 1 or ARGV[0].start_with? '-'
	puts "usage: oak [-v] [-c] [-w] [filename]"
	exit
end

begin
	Proof.process ARGV[0], :is_filename, options
rescue ProofException
	# already printed
rescue Interrupt
	puts "\naborted due to ctrl-c"
rescue => e
	puts "\n\n#{e.message} (#{e.class}) [#{name_version}]"
  puts "\tfrom #{e.backtrace.join "\n\tfrom "}"
	puts "\nBUG: You have found a bug in the proof checker!  It would be " \
       "greatly appreciated if you could report it at #{issues_url} so that " \
       "it can be fixed."
end