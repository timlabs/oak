require_relative 'proof.rb'

name_version = 'Oak version 0.7.1'
issues_url = 'https://github.com/timlabs/oak/issues'

options = {}

if ARGV.delete '-v'
	puts name_version
	exit if ARGV.size == 0
end

if ARGV.delete '-c'
	options[:reduce] = true
end

if ARGV.delete '-f'
	options[:fix] = true
end

if ARGV.delete '-m'
	options[:marker] = true
end

if ARGV.delete '-w'
	options[:wait] = true
end

if options[:fix] and options[:wait]
  puts 'error: options -f and -w cannot be used together'
  exit
end

if ARGV.size != 1 or ARGV[0].start_with? '-'
	puts 'usage: oak [-v] [-c] [-f] [-m] [-w] <filename>'
  puts '  -v  print the version number of Oak'
  puts '  -c  check for unneeded citations'
  puts '  -f  look for a fix'
  puts '  -m  assume until marker'
  puts '  -w  wait for validity (does not change proof outcome)'
	exit
end

begin
	Proof.process_file ARGV[0], options
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