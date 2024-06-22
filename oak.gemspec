Gem::Specification.new {|s|
  s.name        = 'oakproof'
  s.version     = '0.7.1'
  s.date        = '2024-06-21'
  s.summary     = 'A proof checker focused on simplicity, readability, and ' +
                  'ease of use.'
  s.author      = 'Tim Smith'
  s.homepage    = 'http://oakproof.org/'
  s.license     = 'AGPL-3.0'

  s.required_ruby_version = '>= 2.0'

  s.files = Dir['src/*'] + Dir['eprover/*']

  s.bindir = '.'
  s.executables << 'oak'
}