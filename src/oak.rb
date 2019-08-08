if RUBY_VERSION < '2'
	puts "Oak requires Ruby version >= 2.0.  (You have Ruby #{RUBY_VERSION}.)"
	exit
end

require_relative 'proof.rb'

name_version = 'Oak version 0.2pre'
issues_url = 'https://github.com/smithtim/oak/issues'

if ARGV.delete '-v'
	puts name_version
	exit if ARGV.size == 0
end

if ARGV.size != 1 or ARGV[0].start_with? '-'
	puts "usage: oak [-v] [filename]"
	exit
end

begin
	Proof.process ARGV[0], :is_filename
rescue => e
	exit if e.is_a? ProofException # already printed
	puts "\n\n#{e.message} (#{e.class}) [#{name_version}]"
  puts "\tfrom #{e.backtrace.join "\n\tfrom "}"
	puts "\nBUG: You have found a bug in the proof checker!  It would be " \
       "greatly appreciated if you could report it at #{issues_url} so that " \
       "it can be fixed."
end