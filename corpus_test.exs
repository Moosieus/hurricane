defmodule CorpusTest do
  def test_file(path) do
    code = File.read!(path)
    case Hurricane.parse(code) do
      {:ok, _} -> IO.puts("✓ #{Path.basename(path)}")
      {:ok, _, errors} -> IO.puts("⚠ #{Path.basename(path)} - #{length(errors)} errors")
      {:error, reason} -> IO.puts("✗ #{Path.basename(path)} - #{inspect(reason)}")
    end
  rescue
    e -> IO.puts("✗ #{Path.basename(path)} - CRASHED: #{Exception.message(e)}")
  end
end

IO.puts("VALID FILES:")
Path.wildcard("test_corpus/valid/*.ex") |> Enum.each(&CorpusTest.test_file/1)

IO.puts("\nINCOMPLETE FILES:")
Path.wildcard("test_corpus/incomplete/*.ex") |> Enum.each(&CorpusTest.test_file/1)

IO.puts("\nMALFORMED FILES:")
Path.wildcard("test_corpus/malformed/*.ex") |> Enum.each(&CorpusTest.test_file/1)

IO.puts("\nADVERSARIAL FILES:")
Path.wildcard("test_corpus/adversarial/*.ex") |> Enum.each(&CorpusTest.test_file/1)
