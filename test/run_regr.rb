#!/usr/bin/env ruby

require 'rubygems'
require 'pathname'
require 'colorize'
require 'timeout'
require 'getopt/std'

TestDir = Pathname.new(__FILE__).realpath.dirname
BuildDir = Pathname.new(ENV['BUILD_DIR'] || Dir.pwd).realpath
LibPath = "#{BuildDir}/lib/std:#{BuildDir}/lib/ieee"
Opts = Getopt::Std.getopts('v')

def read_tests
  tests = []
  File.open(TestDir + "regress/testlist.txt").each_line do |l|
    parts = l.gsub(/\#.*$/, '').strip.split(/\s+/)
    if parts.length > 0 then
      flags = parts[1].split /,/
      tests << { :name => parts[0], :flags => flags }
    end
  end
  tests
end

def valgrind
  if Opts['v'] then
    'valgrind '
  else
    ''
  end
end

def nvc
  "#{valgrind}#{BuildDir}/src/nvc"
end

def run_cmd(c, invert=false)
  File.open('out', 'a') do |f|
    f.puts c
  end
  
  pid = fork
  exec("exec #{c} >>out 2>&1") if pid.nil?
  begin
    timeout(Opts['v'] ? 10 : 3) do
      Process.wait
      fail unless $?.exitstatus == (invert ? 1 : 0)
    end
  rescue Timeout::Error
    Process.kill 'TERM', pid
    raise
  end
end

def analyse(t)
  run_cmd "#{nvc} -a #{TestDir}/regress/#{t[:name]}.vhd"
end

def elaborate(t)
  run_cmd "#{nvc} -e #{t[:name]}"
end

def run(t)
  stop = ""
  t[:flags].each do |f|
    stop = "--stop-time=#{Regexp.last_match(1)}" if f =~ /stop=(.*)/
  end
  run_cmd "#{nvc} -r #{stop} #{t[:name]}", t[:flags].member?('fail')
end

def check(t)
  if t[:flags].member? 'gold' then
    fname = TestDir + "regress/gold/#{t[:name]}.txt"
    out_lines = File.open('out').lines
    File.open(fname).each_line do |match_line|
      unless out_lines.any? do |output_line|
          output_line.include? match_line.chomp
        end
      then
        puts "failed (no match)".red
        print match_line.chomp
        return false
      end
    end
  end
  print "ok".green
  return true
end

def mkdir_p(n)
  begin
    Dir.mkdir n
  rescue Errno::EEXIST
  end
end

mkdir_p 'logs'
Dir.chdir 'logs'

ENV['NVC_LIBPATH'] = LibPath

passed = 0
failed = 0

read_tests.each do |t|
  printf "%15s : ", t[:name]
  mkdir_p t[:name]
  Dir.chdir t[:name] do
    File.unlink 'out' if File.exists? 'out'
    begin
      analyse t
      elaborate t
      run t
      if check t then
        passed += 1
      else
        failed += 1
      end
    rescue RuntimeError
      puts "failed".red
      File.open('out').each_line do |l|
        puts l
      end
      failed += 1
    rescue Timeout::Error
      puts "failed (timeout)".red
      failed += 1
    end
    puts
  end
end

exit failed
