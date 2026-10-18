"""Regression checks for audit failure modes, not mathematical proof tests."""
import unittest
import verify


class AuditTests(unittest.TestCase):
    def test_nested_comments(self):
        text = "namespace N\n/- outer /- inner -/ theorem hidden : False := bad -/\ntheorem visible : True := trivial\n"
        self.assertEqual(verify.THEOREM_RE.findall(verify.strip_comments(text)), ["visible"])

    def test_line_comments_and_strings(self):
        text = 'def label := "-- /- harmless -/" -- comment\nlemma visible : True := trivial\n'
        result = verify.strip_comments(text)
        self.assertIn('"-- /- harmless -/"', result)
        self.assertNotIn('-- comment', result)
        self.assertEqual(verify.THEOREM_RE.findall(result), ['visible'])

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError):
            verify.strip_comments('/- unfinished')

    def test_type_error_is_not_mathematical_evidence(self):
        self.assertIsNone(verify.MATH_FAILURE.search('error: type mismatch'))

    def test_infrastructure_failure_overrides_unsolved_goal(self):
        text = 'unknown identifier missing\nunsolved goals'
        self.assertIsNotNone(verify.INFRA_FAILURE.search(text))

    def test_unsolved_goal_is_detected(self):
        self.assertIsNotNone(verify.MATH_FAILURE.search('error: unsolved goals'))


if __name__ == '__main__':
    unittest.main()
